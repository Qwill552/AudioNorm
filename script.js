(function () {
    'use strict'

    const VERSION = '0.4.2' // keep in sync with metadata.json
    const ADDON_NAME = 'AudioNorm'
    const TAG = '[AudioNorm]'
    const CACHE_KEY = 'audionorm:cache:v2'
    // v1 could hold values measured from the wrong file (URL taken from the <audio> element)
    const LEGACY_CACHE_KEYS = ['audionorm:cache:v1']
    const CACHE_LIMIT = 5000
    const HOOK_STAGE = -100 // run before the built-in WebAudioPlugin tap (stage 0)
    const TP_MARGIN_DB = 0.5 // sample peak underestimates true peak; stay on the safe side
    const BUILTIN_TARGET_LUFS = -23 // target used by the built-in r128 normalization
    const DURATION_TOLERANCE_MS = 1500
    // Not yet measured UGC tracks get an estimate instead of the client's {i: 0, tp: 0}
    // (= -23 dB) or "leave as is": a typical loudness of the user's measured tracks, taken
    // from the loud side (75th percentile), so a track rather starts a bit quiet than loud.
    const DEFAULT_ESTIMATE_LUFS = -8
    const ESTIMATE_MIN_SAMPLES = 5
    const ESTIMATE_PERCENTILE = 0.75
    const LOOKAHEAD = 3 // upcoming tracks measured in the background
    // Decoded audio takes about 21 MB per minute (stereo, 44.1 kHz, float). MP3 is therefore
    // decoded piece by piece (~60 MB of PCM at a time), so even hour-long mixes fit in memory.
    // Other formats (M4A etc.) cannot be cut that simply and are decoded whole, within limits.
    const LONG_TRACK_MS = 15 * 60 * 1000 // longer = "long track", see the measureLong setting
    const MAX_TRACK_MS = 3 * 60 * 60 * 1000 // hard cap: not even a long track
    const PIECE_BYTES = 4 * 1024 * 1024
    const TAIL_KEEP_BYTES = 64 * 1024 // carried into the next piece, so the last piece is never tiny
    const MAX_JUNK_TAIL_BYTES = 16 * 1024
    const MAX_WHOLE_FILE_BYTES = 40 * 1024 * 1024 // non-MP3, duration known and not long
    const MAX_WHOLE_UNKNOWN_BYTES = 12 * 1024 * 1024 // non-MP3, duration not known yet
    const LONG_DOWNLOAD_TIMEOUT_MS = 30 * 60 * 1000
    const LONG_JOB_TIMEOUT_MS = 40 * 60 * 1000

    // Every await of a measurement is bounded, so a hung request can never block the queue.
    const FILE_INFO_TIMEOUT_MS = 15000
    const STALL_TIMEOUT_MS = 15000 // no bytes from the server for this long = hung download
    const DOWNLOAD_TIMEOUT_MS = 180000
    const DECODE_TIMEOUT_MS = 60000
    const JOB_TIMEOUT_MS = 300000 // backstop for the whole measurement

    const log = (...args) => console.log(TAG, ...args)
    const warn = (...args) => console.warn(TAG, ...args)

    if (window.__audionormLoaded) return
    window.__audionormLoaded = true

    const sleep = ms => new Promise(r => setTimeout(r, ms))
    const obsValue = o => (o && typeof o === 'object' && 'value' in o ? o.value : o)

    // Measurement stopped on purpose (addon disabled, playlist run cancelled, track skipped):
    // not counted as a failed attempt.
    class Cancelled extends Error {}
    // Will fail the same way every time: no retries.
    class Permanent extends Error {}
    // Long track while measuring long tracks is turned off: retried once it is turned on.
    class SkippedLong extends Cancelled {}

    // ---------- settings ----------

    const DEFAULTS = { enabled: true, maxWaitMs: 1500, measureQueue: false, measureLong: true, debug: false }

    function unwrap(entry, fallback) {
        if (entry && typeof entry === 'object' && !Array.isArray(entry)) {
            if (entry.value !== undefined) return entry.value
            if (entry.default !== undefined) return entry.default
            return fallback
        }
        return entry !== undefined ? entry : fallback
    }

    function readSettings() {
        let raw = {}
        try {
            raw = window.pulsesyncApi?.getSettings?.(ADDON_NAME)?.getCurrent?.() ?? {}
        } catch {}
        const maxWait = Number(unwrap(raw.maxWaitMs, DEFAULTS.maxWaitMs))
        return {
            enabled: Boolean(unwrap(raw.enabled, DEFAULTS.enabled)),
            maxWaitMs: Number.isFinite(maxWait) ? Math.max(0, Math.min(maxWait, 5000)) : DEFAULTS.maxWaitMs,
            measureQueue: Boolean(unwrap(raw.measureQueue, DEFAULTS.measureQueue)),
            measureLong: Boolean(unwrap(raw.measureLong, DEFAULTS.measureLong)),
            debug: Boolean(unwrap(raw.debug, DEFAULTS.debug)),
        }
    }

    let settings = readSettings()

    function builtinNormalizationEnabled() {
        try {
            return Boolean(window.nativeSettings?.get?.('modSettings.r128Normalization'))
        } catch {
            return null
        }
    }

    // With the built-in normalization off our values are not used at all: do not download
    // anything and do not delay playback. Unknown (null) counts as on.
    const normalizationOff = () => builtinNormalizationEnabled() === false

    // ---------- cache (trackId -> {i, tp}), oldest entries dropped past CACHE_LIMIT ----------

    const cache = new Map()
    let cacheVersion = 0
    try {
        for (const key of LEGACY_CACHE_KEYS) localStorage.removeItem(key)
        const stored = JSON.parse(localStorage.getItem(CACHE_KEY) || '{}')
        for (const [id, v] of Object.entries(stored)) {
            if (Number.isFinite(v?.i) && Number.isFinite(v?.tp)) cache.set(id, { i: v.i, tp: v.tp })
        }
    } catch (e) {
        warn('cache load failed', e)
    }

    let saveTimer = null
    function saveCache() {
        clearTimeout(saveTimer)
        saveTimer = setTimeout(() => {
            try {
                localStorage.setItem(CACHE_KEY, JSON.stringify(Object.fromEntries(cache)))
            } catch (e) {
                warn('cache save failed', e)
            }
        }, 500)
    }

    function cacheSet(id, value) {
        cache.delete(id)
        cache.set(id, value)
        while (cache.size > CACHE_LIMIT) cache.delete(cache.keys().next().value)
        cacheVersion++
        saveCache()
    }

    // ---------- loudness (ITU-R BS.1770-4 / EBU R128) ----------

    function kWeightingCoeffs(fs) {
        // High shelf + RLB high-pass, coefficients as in libebur128 (valid for any fs)
        let f0 = 1681.974450955533
        const G = 3.999843853973347
        let Q = 0.7071752369554196
        let K = Math.tan((Math.PI * f0) / fs)
        const Vh = Math.pow(10, G / 20)
        const Vb = Math.pow(Vh, 0.4996667741545416)
        let a0 = 1 + K / Q + K * K
        const shelf = {
            b: [(Vh + (Vb * K) / Q + K * K) / a0, (2 * (K * K - Vh)) / a0, (Vh - (Vb * K) / Q + K * K) / a0],
            a: [(2 * (K * K - 1)) / a0, (1 - K / Q + K * K) / a0],
        }
        f0 = 38.13547087602444
        Q = 0.5003270373238773
        K = Math.tan((Math.PI * f0) / fs)
        a0 = 1 + K / Q + K * K
        const hp = { b: [1, -2, 1], a: [(2 * (K * K - 1)) / a0, (1 - K / Q + K * K) / a0] }
        return [shelf, hp]
    }

    // Fed with decoded audio piece by piece: filter state, the 100 ms segment powers and the
    // peak carry over between pieces. Async with periodic yields so the UI does not freeze.
    class LoudnessMeter {
        constructor() {
            this.fs = 0
            this.samples = 0 // per channel, over all pieces
            this.segPower = []
            this.peak = 0
            this.state = []
        }

        async push(channels, fs, signal) {
            if (!this.fs) {
                this.fs = fs
                this.step = Math.round(fs * 0.1) // 100 ms segments
                const [s, h] = kWeightingCoeffs(fs)
                this.s = s
                this.h = h
                this.state = channels.map(() => ({ sx1: 0, sx2: 0, sy1: 0, sy2: 0, hx1: 0, hx2: 0, hy1: 0, hy2: 0 }))
            }
            if (fs !== this.fs || channels.length !== this.state.length) throw new Error('формат аудио поменялся посреди файла')
            const { s, h, step, segPower } = this
            const SEGS_PER_YIELD = 50 // ~5 s of audio per slice
            const n = channels[0].length
            let peak = this.peak
            for (let c = 0; c < channels.length; c++) {
                const x = channels[c]
                let { sx1, sx2, sy1, sy2, hx1, hx2, hy1, hy2 } = this.state[c]
                let g = this.samples // position of x[0] in the whole track
                let i = 0
                let slices = 0
                while (i < n) {
                    const seg = Math.floor(g / step)
                    const end = Math.min(n, i + (step - (g % step)))
                    let sum = 0
                    for (; i < end; i++, g++) {
                        const xi = x[i]
                        const ax = xi < 0 ? -xi : xi
                        if (ax > peak) peak = ax
                        const sy = s.b[0] * xi + s.b[1] * sx1 + s.b[2] * sx2 - s.a[0] * sy1 - s.a[1] * sy2
                        sx2 = sx1; sx1 = xi; sy2 = sy1; sy1 = sy
                        const hy = sy - 2 * hx1 + hx2 - h.a[0] * hy1 - h.a[1] * hy2
                        hx2 = hx1; hx1 = sy; hy2 = hy1; hy1 = hy
                        sum += hy * hy
                    }
                    segPower[seg] = (segPower[seg] ?? 0) + sum // channel weight 1.0 for L/R
                    if (++slices % SEGS_PER_YIELD === 0) {
                        await sleep(0)
                        if (signal.aborted) throw signal.reason
                    }
                }
                this.state[c] = { sx1, sx2, sy1, sy2, hx1, hx2, hy1, hy2 }
            }
            this.peak = peak
            this.samples += n
        }

        result() {
            // only complete 100 ms segments; 400 ms blocks, 75 % overlap = 4 consecutive segments
            const step = this.step
            const nSeg = step ? Math.floor(this.samples / step) : 0
            const p = this.segPower
            const lufs = v => -0.691 + 10 * Math.log10(v)
            const blocks = []
            for (let i = 0; i + 4 <= nSeg; i++) blocks.push((p[i] + p[i + 1] + p[i + 2] + p[i + 3]) / (4 * step))
            const samplePeakDb = 20 * Math.log10(this.peak || 1e-9)
            const absGated = blocks.filter(v => lufs(v) > -70)
            if (!absGated.length) return { integrated: -Infinity, samplePeakDb }
            const relGate = lufs(absGated.reduce((a, b) => a + b, 0) / absGated.length) - 10
            const gated = absGated.filter(v => lufs(v) > relGate)
            return { integrated: lufs(gated.reduce((a, b) => a + b, 0) / gated.length), samplePeakDb }
        }
    }

    // ---------- player access ----------

    let player = null

    const getState = () => player?.state ?? window.sonataState ?? null
    const metaOf = entity => entity?.data?.meta ?? entity?.entityData?.meta ?? null
    const getMediaPlayer = () => obsValue(getState()?.currentMediaPlayer) ?? null

    function getCurrentEntity() {
        const ce = obsValue(getState()?.queueState?.currentEntity)
        return ce?.entity ?? null
    }

    function getQueueEntities() {
        const list = obsValue(getState()?.queueState?.entityList)
        if (!Array.isArray(list)) return []
        return list.map(item => item?.entity ?? item).filter(e => metaOf(e))
    }

    // Measurements never read the <audio> element (it may hold another track); used only for
    // the debug report and for track-boundary timing in the start hook.
    function getCurrentAudioElement() {
        const mp = getMediaPlayer()
        const el = obsValue(mp?.currentAudioElement) ?? obsValue(mp?.currentMediaPlayer?.currentAudioElement)
        return el instanceof HTMLAudioElement ? el : null
    }

    function getNextEntity() {
        return obsValue(getState()?.queueState?.nextEntity)?.entity ?? getMediaPlayer()?.nextContextEntityPair?.entity ?? null
    }

    // The player stores the get-file-info result on the entity itself, so it always
    // belongs to this very track (even when playback goes through MediaSource).
    function getDownloadInfo(entity) {
        const d = entity?.mediaSourceData?.data
        return d && typeof d === 'object' ? d : null
    }

    // Returns { url } or { reason }.
    function urlFromDownloadInfo(di) {
        const url = (Array.isArray(di.urls) && di.urls[0]) || di.url
        if (di.key || (di.transport && di.transport !== 'raw')) {
            return { reason: `файл зашифрован (${di.transport || 'key'})` }
        }
        return url ? { url } : { reason: 'в downloadInfo нет ссылки' }
    }

    // ---------- get-file-info through the client's own media provider ----------

    // The provider signs get-file-info requests with the client's secret; its
    // getFileInfoFromResource() is side-effect free (unlike getMediaSource(), which
    // writes entity.mediaSourceData), so it is safe to call for any track in the queue.
    const FALLBACK_CODECS = ['mp3', 'aac', 'he-aac', 'aac-mp4', 'he-aac-mp4']

    // YM 5.122: mediaPlayer.mediaProvider (composite) .getFileInfoProvider; older builds
    // had getFileInfoFromResource directly on mediaProvider.
    const PROVIDER_LINKS = ['mediaProvider', 'getFileInfoProvider']

    function findMediaProvider() {
        const mp = getMediaPlayer()
        const store = obsValue(getState()?.mediaPlayersStore)
        let level = [mp, mp?.currentMediaPlayer, mp?.firstMediaPlayer, mp?.secondMediaPlayer]
        if (store && typeof store === 'object') level.push(...Object.values(store))
        const seen = new Set()
        for (let depth = 0; depth < 4 && level.length; depth++) {
            const next = []
            for (const c of level) {
                if (!c || typeof c !== 'object' || seen.has(c)) continue
                seen.add(c)
                if (typeof c.getFileInfoFromResource === 'function') return c
                for (const k of PROVIDER_LINKS) next.push(c[k])
            }
            level = next
        }
        return null
    }

    async function fetchFileInfoUrl(meta, signal) {
        const provider = findMediaProvider()
        if (!provider) throw new Error('media provider не найден')
        const codecs = Array.isArray(provider.codecs) && provider.codecs.length ? provider.codecs : FALLBACK_CODECS
        const res = await bounded(
            provider.getFileInfoFromResource({ trackId: String(meta.id), quality: 'nq', codecs, transports: ['raw'] }),
            signal,
            FILE_INFO_TIMEOUT_MS,
            'get-file-info не ответил',
        )
        const di = res?.downloadInfo
        if (!di || typeof di !== 'object') throw new Error('get-file-info: пустой ответ')
        if ('error' in di) throw new Error('get-file-info: ' + String(di.error))
        const r = urlFromDownloadInfo(di)
        if (!r.url) throw new Error(r.reason)
        return r.url
    }

    // ---------- bounded waits ----------

    // Resolves with `promise`, or rejects on timeout / abort. The underlying operation
    // may keep running (decodeAudioData cannot be cancelled), its result is then ignored.
    function bounded(promise, signal, ms, timeoutMessage) {
        return new Promise((resolve, reject) => {
            if (signal.aborted) return reject(signal.reason)
            const done = () => {
                clearTimeout(timer)
                signal.removeEventListener('abort', onAbort)
            }
            const onAbort = () => {
                done()
                reject(signal.reason)
            }
            const timer = setTimeout(() => {
                done()
                reject(new Error(timeoutMessage))
            }, ms)
            signal.addEventListener('abort', onAbort, { once: true })
            Promise.resolve(promise).then(
                v => {
                    done()
                    resolve(v)
                },
                e => {
                    done()
                    reject(e)
                },
            )
        })
    }

    // Streaming download. read() fails when the server sends nothing for STALL_TIMEOUT_MS
    // (a slow but progressing download is fine) or the whole download exceeds the total
    // timeout (extend() raises it for long tracks). Only our own copy of the file is
    // affected; playback uses the player's requests.
    async function openDownload(url, signal) {
        const ctl = new AbortController()
        const onAbort = () => ctl.abort(signal.reason)
        signal.addEventListener('abort', onAbort, { once: true })
        let stallTimer = null
        let totalTimer = null
        const fail = e => ctl.abort(e)
        const extend = ms => {
            clearTimeout(totalTimer)
            totalTimer = setTimeout(() => fail(new Error(`загрузка не уложилась в ${Math.round(ms / 60000)} мин`)), ms)
        }
        const close = () => {
            clearTimeout(stallTimer)
            clearTimeout(totalTimer)
            signal.removeEventListener('abort', onAbort)
            if (!ctl.signal.aborted) ctl.abort(new Cancelled('загрузка закрыта'))
        }
        const reason = e => (ctl.signal.aborted && ctl.signal.reason ? ctl.signal.reason : e)
        extend(DOWNLOAD_TIMEOUT_MS)
        let res
        try {
            if (signal.aborted) throw signal.reason
            stallTimer = setTimeout(() => fail(new Error('загрузка зависла')), STALL_TIMEOUT_MS)
            res = await fetch(url, { signal: ctl.signal })
            clearTimeout(stallTimer)
            if (!res.ok) throw new Error('HTTP ' + res.status)
        } catch (e) {
            const r = reason(e)
            close()
            throw r
        }
        let reader = res.body?.getReader?.() ?? null
        let whole = reader ? null : res // no streaming body: one read of everything
        return {
            contentLength: Number(res.headers?.get?.('content-length')) || 0,
            extend,
            close,
            async read() {
                try {
                    if (whole) {
                        const r = whole
                        whole = null
                        return new Uint8Array(await r.arrayBuffer())
                    }
                    if (!reader) return null
                    stallTimer = setTimeout(() => fail(new Error('загрузка зависла')), STALL_TIMEOUT_MS)
                    const { done, value } = await reader.read()
                    if (done) reader = null
                    return done ? null : value
                } catch (e) {
                    throw reason(e)
                } finally {
                    clearTimeout(stallTimer)
                }
            },
        }
    }

    function concatBytes(chunks, size) {
        if (chunks.length === 1 && chunks[0].byteLength === size) return chunks[0]
        const out = new Uint8Array(size)
        let offset = 0
        for (const c of chunks) {
            out.set(c, offset)
            offset += c.byteLength
        }
        return out
    }

    function isMp3(b) {
        if (b[0] === 0x49 && b[1] === 0x44 && b[2] === 0x33) return true // ID3 tag
        return b[0] === 0xff && (b[1] & 0xe0) === 0xe0 && (b[1] & 0x06) !== 0 // frame sync, layer I-III
    }

    // First frame header after an optional ID3v2 tag: its version/layer and sample-rate
    // bits identify the following frames.
    function firstMp3Header(b) {
        let i = 0
        if (b[0] === 0x49 && b[1] === 0x44 && b[2] === 0x33 && b.length > 10) {
            i = 10 + ((b[6] & 0x7f) << 21) + ((b[7] & 0x7f) << 14) + ((b[8] & 0x7f) << 7) + (b[9] & 0x7f)
            if (b[5] & 0x10) i += 10 // footer
        }
        for (; i + 2 < b.length; i++) if (b[i] === 0xff && (b[i + 1] & 0xe0) === 0xe0) return [b[i + 1], (b[i + 2] >> 2) & 3]
        return null
    }

    // Last frame start in b before end that looks like ref, so a piece ends on a frame
    // boundary. A false match only costs one damaged frame: the decoder resyncs.
    function lastMp3FrameStart(b, ref, end) {
        for (let i = Math.min(b.length - 4, end); i > 0; i--) {
            if (b[i] !== 0xff || b[i + 1] !== ref[0]) continue
            const br = b[i + 2] >> 4
            if (br !== 0 && br !== 15 && ((b[i + 2] >> 2) & 3) === ref[1]) return i
        }
        return -1
    }

    function decodePiece(bytes, signal) {
        return bounded(
            new OfflineAudioContext(1, 1, 44100).decodeAudioData(bytes.slice().buffer),
            signal,
            DECODE_TIMEOUT_MS,
            'декодирование зависло',
        )
    }

    // Downloads and measures a file. MP3 is decoded in PIECE_BYTES pieces cut on frame
    // boundaries while it downloads; anything else is downloaded and decoded whole.
    async function measureFile(url, signal, job, expectedMs, pieceBytes = PIECE_BYTES) {
        const meter = new LoudnessMeter()
        let decodedMs = 0
        let pieces = 0
        let format = null
        let ref = null
        let acc = []
        let accBytes = 0
        const dl = await openDownload(url, signal)
        const markLong = () => {
            if (job.long) return
            job.long = true
            if (!settings.measureLong) throw new SkippedLong('длинный трек, замер длинных треков выключен')
            job.extend?.(LONG_JOB_TIMEOUT_MS)
            dl.extend(LONG_DOWNLOAD_TIMEOUT_MS)
        }
        const flush = async final => {
            const buf = concatBytes(acc, accBytes)
            let cut = buf.length
            if (!final && format === 'mp3') {
                // at most pieceBytes per piece, and the rest is never a lone frame (one MP3
                // frame alone does not decode): keep some bytes for the next piece
                const end = Math.min(pieceBytes, buf.length - Math.min(TAIL_KEEP_BYTES, pieceBytes >> 2))
                ref = ref ?? firstMp3Header(buf)
                const c = ref ? lastMp3FrameStart(buf, ref, end) : -1
                cut = c > 0 ? c : end
            }
            let audio
            try {
                audio = await decodePiece(buf.subarray(0, cut), signal)
            } catch (e) {
                if (signal.aborted) throw signal.reason
                // a few trailing bytes (tag, cut-off frame) that are not audio: nothing to lose
                if (final && pieces && cut < MAX_JUNK_TAIL_BYTES) return
                throw new Error(`не удалось декодировать кусок ${pieces + 1} (${cut} байт): ${e?.message || e}`)
            }
            acc = cut < buf.length ? [buf.subarray(cut)] : []
            accBytes = buf.length - cut
            pieces++
            decodedMs += audio.duration * 1000
            if (decodedMs > MAX_TRACK_MS + DURATION_TOLERANCE_MS) throw new Permanent('трек длиннее 3 ч, не измеряется')
            if (decodedMs > LONG_TRACK_MS + DURATION_TOLERANCE_MS) markLong()
            const channels = []
            for (let c = 0; c < Math.min(audio.numberOfChannels, 2); c++) channels.push(audio.getChannelData(c))
            await meter.push(channels, audio.sampleRate, signal)
        }
        try {
            for (;;) {
                const chunk = await dl.read()
                if (!chunk) break
                acc.push(chunk)
                accBytes += chunk.byteLength
                if (!format && accBytes >= 4) {
                    format = isMp3(concatBytes(acc, accBytes)) ? 'mp3' : 'other'
                    if (format === 'mp3') {
                        if (expectedMs > LONG_TRACK_MS) markLong()
                    } else if (expectedMs > LONG_TRACK_MS) {
                        throw new Permanent('длинные треки в этом формате не измеряются')
                    }
                }
                if (format === 'other') {
                    const cap = expectedMs ? MAX_WHOLE_FILE_BYTES : MAX_WHOLE_UNKNOWN_BYTES
                    if (Math.max(dl.contentLength, accBytes) > cap) throw new Permanent('файл слишком большой для замера')
                }
                while (format === 'mp3' && accBytes >= pieceBytes) await flush(false)
            }
            if (accBytes) await flush(true)
        } finally {
            dl.close()
        }
        return { result: meter.result(), decodedMs, pieces }
    }

    // ---------- track classification ----------

    const UUID_RE = /^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$/i

    // Queue entries the player has not loaded yet carry only the id: a UUID id without
    // trackSource is an uploaded track. Anything with another trackSource is left alone.
    function isUgc(meta) {
        if (!meta) return false
        if (meta.trackSource === 'UGC' || meta.trackSource === 'OWN_REPLACED_TO_UGC') return true
        return meta.trackSource == null && UUID_RE.test(String(meta.id))
    }

    const isOurs = r128 => Boolean(r128 && r128.__audionorm)

    // ---------- writing / reverting meta.r128 ----------

    // Every meta we wrote to, with what was there before, so that disabling the addon
    // can put everything back. WeakRefs: the player may drop metas at any time.
    let touched = []
    let originals = new WeakMap() // meta -> { had, value }

    function writeR128(meta, value) {
        if (!originals.has(meta)) {
            originals.set(meta, { had: Object.prototype.hasOwnProperty.call(meta, 'r128'), value: meta.r128 })
            touched.push(new WeakRef(meta))
        }
        meta.r128 = value
    }

    function revertAll() {
        let reverted = 0
        for (const ref of touched) {
            const meta = ref.deref()
            if (!meta || !isOurs(meta.r128)) continue // gone, or replaced by someone else
            const o = originals.get(meta)
            try {
                if (o?.had) meta.r128 = o.value
                else delete meta.r128
                reverted++
            } catch (e) {
                warn('cannot revert r128', meta.id, e)
            }
        }
        touched = []
        originals = new WeakMap()
        queueSig = null
        return reverted
    }

    function pruneTouched() {
        if (touched.length > 500) touched = touched.filter(ref => ref.deref())
    }

    let estimate = { version: -1, i: DEFAULT_ESTIMATE_LUFS }

    function estimatedLoudness() {
        if (estimate.version === cacheVersion) return estimate.i
        const values = Array.from(cache.values(), v => v.i).filter(Number.isFinite)
        let i = DEFAULT_ESTIMATE_LUFS
        if (values.length >= ESTIMATE_MIN_SAMPLES) {
            values.sort((a, b) => a - b)
            i = Math.round(values[Math.floor(values.length * ESTIMATE_PERCENTILE)] * 2) / 2
        }
        estimate = { version: cacheVersion, i }
        return i
    }

    // Catalog r128 from Yandex is never touched; only UGC tracks without r128 or with ours.
    function applyToMeta(meta) {
        if (!settings.enabled || !isUgc(meta)) return
        if (meta.r128 && !isOurs(meta.r128)) return
        const cached = cache.get(String(meta.id))
        const cur = meta.r128
        // the playing track keeps the estimate it started with until it is measured:
        // no small volume steps while other tracks' measurements shift the estimate
        if (!cached && cur?.__audionorm === 'placeholder' && String(meta.id) === startedId) return
        const next = cached
            ? { i: cached.i, tp: cached.tp, __audionorm: 'measured' }
            : { i: estimatedLoudness(), tp: 0, __audionorm: 'placeholder' }
        if (cur && cur.i === next.i && cur.tp === next.tp && cur.__audionorm === next.__audionorm) return
        try {
            writeR128(meta, next)
        } catch (e) {
            warn('cannot write r128 into meta', meta.id, e)
        }
    }

    // The whole queue is walked only when it (or the cache) changed, plus a periodic
    // safety pass for in-place mutations. Current and next tracks are cheap: always.
    const FULL_PASS_MS = 10000
    let queueSig = null
    let lastFullPass = 0

    function applyToQueue() {
        if (!settings.enabled) return
        applyToMeta(metaOf(getCurrentEntity()))
        applyToMeta(metaOf(getNextEntity()))
        const list = obsValue(getState()?.queueState?.entityList)
        const sig = [list, Array.isArray(list) ? list.length : -1, cacheVersion]
        const now = Date.now()
        if (queueSig && sig.every((v, i) => v === queueSig[i]) && now - lastFullPass < FULL_PASS_MS) return
        queueSig = sig
        lastFullPass = now
        for (const entity of getQueueEntities()) applyToMeta(metaOf(entity))
        pruneTouched()
    }

    // ---------- measurement queue ----------

    const MAX_ATTEMPTS = 3
    const RETRY_COOLDOWN_MS = 5000

    const inflight = new Map() // trackId -> job
    const failed = new Map() // trackId -> reason, after MAX_ATTEMPTS (no more retries this session)
    const attempts = new Map() // trackId -> failed attempts so far
    const reasons = new Map() // trackId -> last reason why it is not measured (for the badge)
    const retryAt = new Map() // trackId -> timestamp before which we do not retry
    // One background measurement at a time (upcoming tracks, playlist run); the playing
    // track's measurement (urgent) may run alongside it so it never waits for a download
    // of some other track.
    const skippedLong = new Set() // long tracks not measured while measureLong is off
    const pending = [] // jobs waiting to run
    const running = new Set()

    // A job: { id, meta, entity, controller, batchOnly, urgent, promise, settle }
    function measureTrack(entity, { urgent = false, batch = false } = {}) {
        const meta = metaOf(entity)
        if (!settings.enabled || !meta) return Promise.resolve(null)
        const id = String(meta.id)
        if (cache.has(id)) return Promise.resolve(cache.get(id))
        const existing = inflight.get(id)
        if (existing) {
            if (!batch) existing.batchOnly = false
            if (urgent && pending.includes(existing)) {
                existing.urgent = true
                pending.splice(pending.indexOf(existing), 1)
                pending.unshift(existing)
                pump()
            }
            return existing.promise
        }
        if (failed.has(id)) return Promise.resolve(null)
        if (skippedLong.has(id) && !settings.measureLong) return Promise.resolve(null)
        if (Date.now() < (retryAt.get(id) ?? 0)) return Promise.resolve(null)

        const job = { id, meta, entity, controller: new AbortController(), batchOnly: batch, urgent }
        job.promise = new Promise(resolve => (job.settle = resolve))
        inflight.set(id, job)
        if (urgent) pending.unshift(job)
        else pending.push(job)
        pump()
        return job.promise
    }

    function canStart(job) {
        if (!running.size) return true
        return job.urgent && running.size === 1 && !Array.from(running).some(j => j.urgent)
    }

    function pump() {
        while (pending.length && canStart(pending[0])) {
            const job = pending.shift()
            // Skipped past while waiting: do not download a track nobody is about to hear.
            if (!job.batchOnly && !isCurrentOrUpcoming(job.id)) {
                finishJob(job, null, new Cancelled('трек уже пропущен'))
                continue
            }
            startJob(job)
        }
    }

    function startJob(job) {
        running.add(job)
        const signal = job.controller.signal
        // backstop for the whole measurement; long tracks raise it
        job.extend = ms => {
            clearTimeout(job.backstop)
            job.backstop = setTimeout(() => job.controller.abort(new Error(`замер не уложился в ${Math.round(ms / 60000)} мин`)), ms)
        }
        job.extend(JOB_TIMEOUT_MS)
        const aborted = new Promise((_, reject) => {
            if (signal.aborted) reject(signal.reason)
            signal.addEventListener('abort', () => reject(signal.reason), { once: true })
        })
        Promise.race([runJob(job), aborted])
            .then(
                value => finishJob(job, value, null),
                e => finishJob(job, null, e),
            )
            .finally(() => {
                clearTimeout(job.backstop)
                running.delete(job)
                pump()
            })
    }

    function finishJob(job, value, error) {
        inflight.delete(job.id)
        if (error instanceof SkippedLong) {
            skippedLong.add(job.id)
            reasons.set(job.id, error.message)
        }
        if (error && !(error instanceof Cancelled)) {
            const reason = error?.message || String(error)
            const n = (attempts.get(job.id) ?? 0) + 1
            attempts.set(job.id, n)
            reasons.set(job.id, reason)
            retryAt.set(job.id, Date.now() + RETRY_COOLDOWN_MS)
            if (n >= MAX_ATTEMPTS || error instanceof Permanent) failed.set(job.id, reason)
            warn(`measure failed for "${job.meta.title}" (attempt ${n}/${MAX_ATTEMPTS}):`, reason)
        }
        job.settle(value)
        if (value) {
            applyToQueue()
            syncBuiltinGain()
        }
        updateBadge()
    }

    function isCurrentOrUpcoming(id) {
        return [getCurrentEntity(), ...getUpcomingEntities()].some(e => String(metaOf(e)?.id ?? '') === id)
    }

    // The file URL comes only from data that belongs to this very track: the player's
    // get-file-info result stored on the entity, or our own get-file-info request.
    async function runJob(job) {
        const { meta, entity, controller } = job
        const signal = controller.signal
        const t0 = performance.now()
        // Unknown for queue entries the player has not loaded yet; the URL is requested
        // by this track's id anyway, the duration check is an extra guard on top.
        const expectedMs = Number(meta.durationMs) || 0
        if (expectedMs > MAX_TRACK_MS) throw new Permanent('трек длиннее 3 ч, не измеряется')
        if (expectedMs > LONG_TRACK_MS && !settings.measureLong) throw new SkippedLong('длинный трек, замер длинных треков выключен')

        // URLs are signed and expire, so resolve right before downloading
        const di = getDownloadInfo(entity)
        let url = di ? urlFromDownloadInfo(di).url : null
        if (!url) url = await fetchFileInfoUrl(meta, signal)

        const { result: r, decodedMs, pieces } = await measureFile(url, signal, job, expectedMs)
        // Guard against measuring the wrong file (piece boundaries may lose a frame or two)
        if (expectedMs && Math.abs(decodedMs - expectedMs) > DURATION_TOLERANCE_MS + pieces * 100) {
            throw new Error(`длительность не совпала: ${Math.round(decodedMs)} vs ${expectedMs} мс`)
        }
        if (!Number.isFinite(r.integrated)) throw new Error('тишина')
        if (signal.aborted) throw signal.reason
        const value = {
            i: Math.round(r.integrated * 100) / 100,
            tp: Math.round((r.samplePeakDb + TP_MARGIN_DB) * 100) / 100,
        }
        cacheSet(job.id, value)
        log(`measured "${meta.title}"`, value, `${Math.round(performance.now() - t0)} ms, ${pieces} piece(s)`)
        return value
    }

    function cancelJobs(predicate, reason) {
        for (let i = pending.length - 1; i >= 0; i--) {
            const job = pending[i]
            if (!predicate(job)) continue
            pending.splice(i, 1)
            finishJob(job, null, new Cancelled(reason))
        }
        for (const job of running) if (predicate(job)) job.controller.abort(new Cancelled(reason))
    }

    function needsMeasure(meta) {
        return isUgc(meta) && (!meta.r128 || isOurs(meta.r128)) && !cache.has(String(meta.id))
    }

    function measureCurrentIfNeeded() {
        const entity = getCurrentEntity()
        if (!needsMeasure(metaOf(entity))) return null
        return measureTrack(entity, { urgent: true })
    }

    // The next LOOKAHEAD tracks: the player's own next entity, then the queue order after
    // the current track (with shuffle the queue order may differ, it is only a guess).
    function getUpcomingEntities() {
        const out = []
        const ids = new Set([String(metaOf(getCurrentEntity())?.id ?? '')])
        const add = e => {
            const id = String(metaOf(e)?.id ?? '')
            if (!id || ids.has(id)) return
            ids.add(id)
            out.push(e)
        }
        add(getNextEntity())
        const list = getQueueEntities()
        const curId = String(metaOf(getCurrentEntity())?.id ?? '')
        const idx = list.findIndex(e => String(metaOf(e)?.id) === curId)
        if (idx >= 0) for (let i = idx + 1; i < list.length && out.length < LOOKAHEAD; i++) add(list[i])
        return out
    }

    // Measured during the current track, so the next ones start with the right volume.
    function measureUpcomingIfNeeded() {
        for (const entity of getUpcomingEntities()) {
            if (needsMeasure(metaOf(entity))) measureTrack(entity)
        }
    }

    // ---------- "measure whole playlist" ----------

    // { total, done, ok, failed, cancelled, finishedAt }
    let batch = null
    let lastMeasureQueueValue = null

    async function runBatch() {
        const seen = new Set()
        const todo = getQueueEntities().filter(e => {
            const meta = metaOf(e)
            const id = String(meta.id)
            if (seen.has(id) || !needsMeasure(meta)) return false
            seen.add(id)
            return true
        })
        const b = { total: todo.length, done: 0, ok: 0, failed: 0, cancelled: false, finishedAt: 0 }
        batch = b
        log('playlist measure: start,', todo.length, 'tracks')
        updateBadge()
        for (const entity of todo) {
            if (b.cancelled) break
            const id = String(metaOf(entity).id)
            // explicit user request: give previously failed tracks a fresh try
            failed.delete(id)
            attempts.delete(id)
            retryAt.delete(id)
            const value = await measureTrack(entity, { batch: true })
            if (b.cancelled) break
            b.done++
            if (value) b.ok++
            else b.failed++
            updateBadge()
        }
        b.finishedAt = Date.now()
        log('playlist measure: finished', b)
        updateBadge()
    }

    function isBatchRunning() {
        return Boolean(batch && !batch.finishedAt)
    }

    function cancelBatch() {
        if (!isBatchRunning()) return
        batch.cancelled = true
        cancelJobs(job => job.batchOnly, 'замер плейлиста остановлен')
    }

    // The settings toggle works as a button: every change starts (or cancels) a run.
    function checkBatchTrigger() {
        const v = settings.measureQueue
        if (lastMeasureQueueValue !== null && v !== lastMeasureQueueValue) {
            if (isBatchRunning()) cancelBatch()
            else if (settings.enabled && !normalizationOff()) runBatch().catch(e => warn('playlist measure failed', e))
            else if (settings.enabled) {
                batch = { total: 0, done: 0, ok: 0, failed: 0, cancelled: false, finishedAt: Date.now(), normalizationOff: true }
                updateBadge()
            }
        }
        lastMeasureQueueValue = v
    }

    // ---------- enable / disable ----------

    function refreshSettings() {
        const prev = settings
        settings = readSettings()
        if (prev.enabled && !settings.enabled) onDisabled()
        else if (!prev.enabled && settings.enabled) onEnabled()
        if (prev.measureLong && !settings.measureLong) cancelJobs(job => job.long, 'замер длинных треков выключен')
        else if (!prev.measureLong && settings.measureLong) {
            for (const id of skippedLong) reasons.delete(id)
            skippedLong.clear()
        }
        checkBatchTrigger()
    }

    // Turning the addon off must leave the player exactly as without it: stop all
    // downloads, remove our r128 from every meta and let the built-in plugin recompute.
    function onDisabled() {
        cancelBatch()
        cancelJobs(() => true, 'AudioNorm выключен')
        const n = revertAll()
        syncBuiltinGain()
        log('disabled: reverted r128 on', n, 'tracks')
    }

    function onEnabled() {
        queueSig = null
        applyToQueue()
        syncBuiltinGain()
        log('enabled')
    }

    // ---------- player hook ----------

    let startHook = null // hook of the playback that owns the current queue
    const tappedHooks = new WeakSet()
    let hookOwners = new Map() // hook -> object it was found on
    const hookPaths = new Map() // hook -> path where it was found (for the debug report)
    let appliedKey = null // "<id>|<i>|<tp>" that the built-in r128 gain node currently uses

    // The wrapper's `state` getter is `this.playbackController.getPlayback().state`,
    // so getPlayback() is the active Sonata Playback that owns `hooks`.
    function currentPlaybacks() {
        const out = []
        for (const w of [player, window.pulsesyncApi?.playerInstance]) {
            try {
                const pb = w?.playbackController?.getPlayback?.()
                if (pb && !out.includes(pb)) out.push(pb)
            } catch {}
        }
        return out
    }

    function playerRoots() {
        const api = window.pulsesyncApi
        let apiState = null
        try {
            apiState = api?.getState?.()
        } catch {}
        return [...currentPlaybacks(), player, api?.playerInstance, window.__pulseSyncPendingPlayerInstance, apiState].filter(
            r => r && typeof r === 'object',
        )
    }

    const HOOK_SEARCH_DEPTH = 6
    const HOOK_SEARCH_MAX_NODES = 4000

    // Fallback when getPlayback() is not available: breadth-first search through own
    // properties of the player wrapper (e.g. Ks { playbackController, ... }).
    function findStartHooks() {
        const found = new Map() // hook -> owner (the object that has `.hooks`)
        const seen = new WeakSet()
        const queue = playerRoots().map((obj, i) => ({ obj, depth: 0, path: `root${i}` }))
        let visited = 0
        while (queue.length && visited < HOOK_SEARCH_MAX_NODES) {
            const { obj, depth, path } = queue.shift()
            if (!obj || typeof obj !== 'object' || seen.has(obj)) continue
            if ((typeof Node !== 'undefined' && obj instanceof Node) || obj instanceof ArrayBuffer || ArrayBuffer.isView(obj)) continue
            seen.add(obj)
            visited++
            let hook = null
            try {
                hook = obj.hooks?.beforeMediaStartPlaying
            } catch {}
            if (typeof hook?.tapPromise === 'function' && !found.has(hook)) {
                found.set(hook, obj)
                if (!hookPaths.has(hook)) hookPaths.set(hook, path + '.hooks')
            }
            if (depth >= HOOK_SEARCH_DEPTH) continue
            let entries = []
            try {
                if (obj instanceof Map) entries = Array.from(obj.entries(), ([k, v]) => [`get(${String(k)})`, v])
                else if (Array.isArray(obj)) entries = obj.slice(0, 50).map((v, i) => [`[${i}]`, v])
                else entries = Object.keys(obj).map(k => [k, obj[k]])
            } catch {}
            for (const [k, v] of entries) {
                if (v && typeof v === 'object') queue.push({ obj: v, depth: depth + 1, path: `${path}.${k}` })
            }
        }
        return found
    }

    function pickActiveHook() {
        const queueState = getState()?.queueState
        let fallback = null
        for (const [hook, owner] of hookOwners) {
            if (queueState && owner?.state?.queueState === queueState) return hook
            fallback = fallback ?? hook
        }
        return hookOwners.size === 1 ? fallback : null
    }

    function useHook(hook, path) {
        if (!hookPaths.has(hook)) hookPaths.set(hook, path)
        if (!tappedHooks.has(hook)) {
            tappedHooks.add(hook)
            tapStartHook(hook)
        }
    }

    // Called every tick, but cheap: normally the active playback's hook is read directly
    // (playbacks are recreated e.g. when switching to My Vibe, this picks up the new one).
    // The object-graph search runs only if that fails: re-checked every 10 s once found,
    // with growing pauses while nothing is found.
    const HOOK_RECHECK_MS = 10000
    const HOOK_SEARCH_BACKOFF_MS = [1000, 2000, 5000, 10000, 30000, 60000]
    let hookSearchFailures = 0
    let nextHookSearchAt = 0

    function installHooks() {
        const queueState = getState()?.queueState
        for (const pb of currentPlaybacks()) {
            let hook = null
            try {
                hook = pb.hooks?.beforeMediaStartPlaying
            } catch {}
            if (typeof hook?.tapPromise !== 'function') continue
            if (queueState && pb.state?.queueState && pb.state.queueState !== queueState) continue
            if (hook !== startHook) {
                useHook(hook, 'playbackController.getPlayback().hooks')
                hookOwners = new Map([[hook, pb]])
                startHook = hook
            }
            hookSearchFailures = 0
            return
        }

        if (Date.now() < nextHookSearchAt) return
        hookOwners = findStartHooks()
        for (const hook of hookOwners.keys()) useHook(hook, hookPaths.get(hook))
        startHook = pickActiveHook()
        if (startHook) {
            hookSearchFailures = 0
            nextHookSearchAt = Date.now() + HOOK_RECHECK_MS
        } else {
            const i = Math.min(hookSearchFailures++, HOOK_SEARCH_BACKOFF_MS.length - 1)
            nextHookSearchAt = Date.now() + HOOK_SEARCH_BACKOFF_MS[i]
        }
    }

    function r128Key(meta) {
        if (!meta) return null
        const r = meta.r128
        return `${meta.id}|${r ? r.i : 'none'}|${r ? r.tp : 'none'}`
    }

    // The built-in normalization only sets the gain in its beforeMediaStartPlaying tap.
    // When r128 of the playing track changes mid-track (measured, or reverted on disable),
    // re-run just that tap: it takes no arguments, re-reads meta.r128 and calls setR128Gain
    // on the graphs (its fade/smartPreview calls are idempotent for the current entity).
    //
    // Only for the track the player has already started (startedId). After a skip,
    // currentEntity switches up to a second or more before beforeMediaStartPlaying while the
    // previous track is still audible on the same audio element; applying the new track's
    // gain then makes the old one jump in volume. The hook applies the right value itself.
    let reapplying = false
    let hookRunning = 0 // our tap is waiting; WebAudioPlugin will apply right after it
    let startedId = null // id of the track beforeMediaStartPlaying last ran for

    function syncBuiltinGain() {
        if (reapplying || hookRunning) return
        const meta = metaOf(getCurrentEntity())
        if (!meta || String(meta.id) !== startedId) return
        const key = r128Key(meta)
        if (!key || key === appliedKey) return
        const tap = startHook?.taps?.find?.(t => t?.name === 'WebAudioPlugin')
        if (typeof tap?.fn !== 'function') return
        appliedKey = key
        reapplying = true
        const done = () => (reapplying = false)
        try {
            bounded(tap.fn(), new AbortController().signal, 5000, 'timeout')
                .catch(e => warn('re-apply failed', e))
                .finally(done)
            log('re-applied built-in r128 gain', meta.r128 ?? '(none)')
        } catch (e) {
            done()
            warn('re-apply failed', e)
        }
    }

    // Until the next track's src is set (after this hook), the <audio> element still holds
    // the previous track. After a natural end the YASP element keeps shouldPlay = true (only
    // its own pause() clears it), so any canplay there, or the player's resume() (media keys),
    // restarts the finished track from 0 until the new src arrives. pause() on an ended
    // element fires no events: it only clears that flag.
    function settleEndedAudio(el) {
        if (!settings.enabled || !el?.ended) return
        try {
            el.pause()
        } catch {}
    }

    const watchedAudio = new WeakSet()

    function watchAudioEnd() {
        const el = getCurrentAudioElement()
        if (!el || watchedAudio.has(el)) return
        watchedAudio.add(el)
        // 'pause' comes right at the end; 'ended' may come only after the next src is set
        for (const type of ['pause', 'ended']) el.addEventListener(type, () => settleEndedAudio(el))
    }

    const END_MARGIN_MS = 300

    // How long the hook may hold the start without hurting the previous track. A finished
    // track waits in the element (see settleEndedAudio): do not stretch that window. A
    // still-playing one (skip near the end) must not end during the wait, or the player
    // treats it as a natural end and advances again, skipping the chosen track.
    function startWaitLimitMs() {
        const el = getCurrentAudioElement()
        if (!el) return settings.maxWaitMs
        const leftMs = ((el.duration - el.currentTime) * 1000) / (el.playbackRate || 1)
        if (el.ended || leftMs < END_MARGIN_MS) return 0
        if (el.paused || !Number.isFinite(leftMs)) return settings.maxWaitMs
        return Math.min(settings.maxWaitMs, leftMs - END_MARGIN_MS)
    }

    function tapStartHook(hook) {
        hook.tapPromise({ name: 'AudioNorm', stage: HOOK_STAGE }, async () => {
            // Must never throw: a rejected tap could break playback start.
            let meta = null
            hookRunning++
            try {
                refreshSettings()
                settleEndedAudio(getCurrentAudioElement())
                meta = metaOf(getCurrentEntity())
                if (settings.enabled && isUgc(meta)) {
                    applyToMeta(meta)
                    if (needsMeasure(meta) && settings.maxWaitMs > 0 && !normalizationOff()) {
                        const p = measureCurrentIfNeeded()
                        const waitMs = startWaitLimitMs()
                        if (p && waitMs > 0) {
                            await Promise.race([p, sleep(waitMs)])
                            applyToMeta(meta)
                        }
                    }
                }
            } catch (e) {
                warn('hook error', e)
            } finally {
                hookRunning--
            }
            // WebAudioPlugin runs right after us with exactly this r128 (also when disabled)
            if (!startHook || hook === startHook) {
                appliedKey = r128Key(meta)
                startedId = meta ? String(meta.id) : null
            }
        })
        log('hooked beforeMediaStartPlaying, built-in tap found:', !!hook.taps?.some?.(t => t?.name === 'WebAudioPlugin'))
    }

    // ---------- badge ----------

    let badge = null

    function builtinGainDb(r128) {
        if (!r128 || !Number.isFinite(r128.i)) return 0
        let g = BUILTIN_TARGET_LUFS - r128.i
        if (Number.isFinite(r128.tp)) g = Math.min(g, -r128.tp)
        return g
    }

    const fmt = n => (n > 0 ? '+' : n < 0 ? '−' : '') + Math.abs(n).toFixed(1)

    const PROBLEM_SHOW_DELAY_MS = 3000 // ignore short transitional states around a track change
    const BATCH_RESULT_SHOW_MS = 6000
    let problemSince = 0
    let copiedUntil = 0

    function batchText(b) {
        if (b.normalizationOff) return 'AN: включите «Нормализация громкости» в настройках звука'
        if (!b.finishedAt) return `AN: измеряю плейлист ${b.done}/${b.total}${b.failed ? `, ошибок ${b.failed}` : ''}`
        if (b.total === 0) return 'AN: в очереди нет неизмеренных загруженных треков'
        const head = b.cancelled ? `AN: замер остановлен, измерено ${b.ok} из ${b.total}` : `AN: плейлист измерен: ${b.ok} из ${b.total}`
        return head + (b.failed ? `, ошибок ${b.failed}` : '')
    }

    // Visible only while a playlist measurement runs (and shortly after),
    // or, in debug mode, while something is wrong. Hidden when everything works.
    function updateBadge() {
        if (!badge) return
        if (Date.now() < copiedUntil) return

        if (batch && (!batch.finishedAt || Date.now() - batch.finishedAt < BATCH_RESULT_SHOW_MS)) {
            badge.hidden = false
            badge.textContent = batchText(batch)
            badge.classList.toggle('warn', batch.failed > 0)
            return
        }

        if (!settings.debug) {
            // status is only ever shown in debug mode, do not compute it
            problemSince = 0
            badge.hidden = true
            return
        }

        const { text, problem } = computeStatus()
        if (!problem) problemSince = 0
        else if (!problemSince) problemSince = Date.now()
        const show = problem && Date.now() - problemSince >= PROBLEM_SHOW_DELAY_MS
        badge.hidden = !show
        if (show) {
            badge.textContent = text
            badge.classList.add('warn')
        }
    }

    function computeStatus() {
        const meta = metaOf(getCurrentEntity())
        const builtinOn = builtinNormalizationEnabled()
        let text = 'AN: —'
        let warnState = false

        if (!settings.enabled) {
            return { text: 'AN: выкл.', problem: false }
        } else if (meta) {
            const id = String(meta.id)
            const r = meta.r128
            if (!isUgc(meta)) {
                text = r ? `AN: каталог ${r.i.toFixed(1)} LUFS → ${fmt(builtinGainDb(r))} dB` : 'AN: каталог, нет r128'
            } else if (inflight.has(id)) {
                text = 'AN: замер…'
            } else if (cache.has(id)) {
                const c = cache.get(id)
                const applied = r && r.__audionorm === 'measured' && appliedKey === r128Key(meta)
                text = `AN: UGC ${c.i.toFixed(1)} LUFS → ${fmt(builtinGainDb(c))} dB${applied ? '' : ' (не применено)'}`
                warnState = !applied
            } else if (skippedLong.has(id) && !settings.measureLong) {
                text = 'AN: длинный трек, замер длинных треков выключен'
            } else if (failed.has(id)) {
                text = `AN: замер не удался: ${failed.get(id)}`
                warnState = true
            } else if (reasons.has(id)) {
                text = `AN: не измерен (${attempts.get(id) ?? 0}/${MAX_ATTEMPTS}): ${reasons.get(id)}`
                warnState = true
            } else {
                text = 'AN: UGC, ещё не измерен'
            }
            if (!startHook) {
                text += hookOwners.size ? ` · хуков ${hookOwners.size}, активный не определён` : ' · хук плеера не найден'
                warnState = true
            }
        }
        if (builtinOn === false) {
            text += ' · r128 в PulseSync выкл.'
            warnState = true
        }
        return { text, problem: warnState }
    }

    // ---------- bootstrap ----------

    async function waitForPlayer() {
        for (let i = 0; i < 150; i++) {
            const p = window.pulsesyncApi?.playerInstance
            if (p) return p
            await sleep(100)
        }
        return null
    }

    // ---------- debug report (click the badge to copy) ----------

    function describe(obj) {
        if (!obj || typeof obj !== 'object') return obj === undefined ? 'undefined' : obj === null ? 'null' : typeof obj
        let own = []
        let proto = []
        try {
            own = Object.keys(obj).slice(0, 60)
        } catch {}
        try {
            const p = Object.getPrototypeOf(obj)
            if (p && p !== Object.prototype) proto = Object.getOwnPropertyNames(p).slice(0, 60)
        } catch {}
        return { ctor: obj.constructor?.name ?? null, own, proto }
    }

    function debugReport() {
        const api = window.pulsesyncApi
        const entity = getCurrentEntity()
        const meta = metaOf(entity)
        const di = getDownloadInfo(entity)
        const nextEntity = getNextEntity()
        const el = getCurrentAudioElement()
        const src = el ? el.currentSrc || el.src || '' : ''
        return {
            version: VERSION,
            settings,
            builtinR128: builtinNormalizationEnabled(),
            status: computeStatus().text,
            mediaProviderFound: !!findMediaProvider(),
            batch,
            measuring: running.size ? Array.from(running, j => j.id).join(',') : null,
            pendingJobs: pending.length,
            touchedMetas: touched.length,
            queueLength: getQueueEntities().length,
            player: describe(player),
            playerInstance: describe(api?.playerInstance),
            playerInstanceIsPlayer: api?.playerInstance === player,
            pendingPlayerInstance: describe(window.__pulseSyncPendingPlayerInstance),
            sonataStateIsPlayerState: !!player?.state && player.state === window.sonataState,
            playbackController: describe(player?.playbackController),
            hooksFound: hookOwners.size,
            hookPaths: Array.from(hookOwners.keys(), h => hookPaths.get(h) ?? null),
            activeHook: !!startHook,
            activeHookTaps: startHook?.taps?.map?.(t => `${t?.name}@${t?.stage ?? 0}`) ?? null,
            appliedKey,
            current: meta
                ? {
                      id: meta.id,
                      title: meta.title,
                      trackSource: meta.trackSource,
                      durationMs: meta.durationMs,
                      r128: meta.r128,
                      cached: cache.get(String(meta.id)) ?? null,
                      reason: reasons.get(String(meta.id)) ?? null,
                      attempts: attempts.get(String(meta.id)) ?? 0,
                      entityKeys: describe(entity).own,
                      mediaSourceData: entity?.mediaSourceData ? describe(entity.mediaSourceData).own : null,
                      downloadInfo: di
                          ? {
                                keys: Object.keys(di),
                                codec: di.codec,
                                transport: di.transport,
                                hasKey: !!di.key,
                                urls: Array.isArray(di.urls) ? di.urls.length : null,
                            }
                          : null,
                  }
                : null,
            next: nextEntity
                ? {
                      title: metaOf(nextEntity)?.title,
                      trackSource: metaOf(nextEntity)?.trackSource,
                      hasDownloadInfo: !!getDownloadInfo(nextEntity),
                  }
                : null,
            audio: el
                ? { scheme: src ? src.split(':')[0] : null, hasSrcObject: !!el.srcObject, duration: el.duration }
                : null,
            cacheSize: cache.size,
            estimateLufs: estimatedLoudness(),
        }
    }

    async function copyDebugReport() {
        const text = JSON.stringify(debugReport(), null, 2)
        try {
            await navigator.clipboard.writeText(text)
        } catch {
            const ta = document.createElement('textarea')
            ta.value = text
            document.body.appendChild(ta)
            ta.select()
            document.execCommand('copy')
            ta.remove()
        }
        badge.textContent = 'AN: отладочный отчёт скопирован'
        copiedUntil = Date.now() + 1500
        setTimeout(updateBadge, 1600)
    }

    async function start() {
        for (let i = 0; i < 100 && !window.pulsesyncApi; i++) await sleep(200)
        player = await waitForPlayer()
        while (!document.body) await sleep(100)

        badge = document.createElement('div')
        badge.id = 'audionorm-badge'
        badge.title = 'Клик — скопировать отладочный отчёт'
        badge.hidden = true
        badge.addEventListener('click', () => copyDebugReport())
        document.body.appendChild(badge)

        settings = readSettings()
        lastMeasureQueueValue = settings.measureQueue // do not start a run on load
        installHooks()
        // loaded mid-track: the playing track started before our hook existed
        if (obsValue(getState()?.playerState?.status) === 'playing') startedId = String(metaOf(getCurrentEntity())?.id ?? '') || null
        applyToQueue()

        try {
            window.pulsesyncApi?.getSettings?.(ADDON_NAME)?.onChange?.(() => {
                refreshSettings()
                applyToQueue()
                updateBadge()
            })
        } catch {}

        let lastId = null
        let lastIdChangedAt = 0
        setInterval(() => {
            refreshSettings()
            installHooks()
            watchAudioEnd()
            if (settings.enabled && !normalizationOff()) {
                applyToQueue()
                const id = String(metaOf(getCurrentEntity())?.id ?? '')
                if (id !== lastId) {
                    lastId = id
                    lastIdChangedAt = Date.now()
                }
                // the hook measures at track start; this is the retry path (with cooldown).
                // The delay skips tracks the user is just flipping through.
                if (Date.now() - lastIdChangedAt > 1500) measureCurrentIfNeeded()
                // tracks skipped past: drop their downloads, the slot is better used ahead
                if (running.size || pending.length) cancelJobs(job => !job.batchOnly && !isCurrentOrUpcoming(job.id), 'трек уже пропущен')
                measureUpcomingIfNeeded()
            }
            syncBuiltinGain()
            updateBadge()
        }, 1000)

        log('started', VERSION, { cached: cache.size, settings, builtinR128: builtinNormalizationEnabled() })
    }

    // Debug helpers in DevTools: __audionorm.status(), __audionorm.clearCache()
    window.__audionorm = {
        cache,
        failed,
        reasons,
        status: debugReport,
        // __audionorm.measure(trackId, pieceBytes?): measures without caching, for checks
        async measure(trackId, pieceBytes = PIECE_BYTES) {
            const controller = new AbortController()
            const url = await fetchFileInfoUrl({ id: trackId }, controller.signal)
            const { result, decodedMs, pieces } = await measureFile(url, controller.signal, { long: true }, 0, pieceBytes)
            return {
                i: Math.round(result.integrated * 100) / 100,
                tp: Math.round((result.samplePeakDb + TP_MARGIN_DB) * 100) / 100,
                durationMs: Math.round(decodedMs),
                pieces,
            }
        },
        clearCache() {
            cache.clear()
            cacheVersion++
            failed.clear()
            attempts.clear()
            reasons.clear()
            retryAt.clear()
            saveCache()
        },
    }

    start().catch(e => console.error(TAG, 'start failed', e))
})()
