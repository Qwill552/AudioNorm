(function () {
    'use strict'

    const ADDON_NAME = 'AudioNorm'
    const TAG = '[AudioNorm]'
    const CACHE_KEY = 'audionorm:cache:v1'
    const HOOK_STAGE = -100 // run before the built-in WebAudioPlugin tap (stage 0)
    const TP_MARGIN_DB = 0.5 // sample peak underestimates true peak; stay on the safe side
    const BUILTIN_TARGET_LUFS = -23 // target used by the built-in r128 normalization
    const DURATION_TOLERANCE_MS = 2500
    // With {i: -23, tp: 0} the built-in formula min(-23 - i, -tp) yields 0 dB, i.e. "leave as is".
    // Without it, the client substitutes {i: 0, tp: 0} for UGC tracks, which means -23 dB.
    const PLACEHOLDER = Object.freeze({ i: BUILTIN_TARGET_LUFS, tp: 0 })

    const log = (...args) => console.log(TAG, ...args)
    const warn = (...args) => console.warn(TAG, ...args)

    if (window.__audionormLoaded) return
    window.__audionormLoaded = true

    const sleep = ms => new Promise(r => setTimeout(r, ms))
    const obsValue = o => (o && typeof o === 'object' && 'value' in o ? o.value : o)

    // ---------- settings ----------

    const DEFAULTS = { enabled: true, maxWaitMs: 1500, measureQueue: false, debug: false }

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

    // ---------- cache (trackId -> {i, tp}) ----------

    const cache = new Map()
    try {
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

    // Async with periodic yields so a long track does not freeze the UI.
    async function measureLoudness(channels, fs) {
        const [s, h] = kWeightingCoeffs(fs)
        const step = Math.round(fs * 0.1) // 100 ms segments
        const nSeg = Math.floor(channels[0].length / step)
        const segPower = new Float64Array(nSeg)
        const SEGS_PER_YIELD = 50 // ~5 s of audio per slice
        let peak = 0

        for (const x of channels) {
            // two cascaded biquads, state kept across slices
            let sx1 = 0, sx2 = 0, sy1 = 0, sy2 = 0
            let hx1 = 0, hx2 = 0, hy1 = 0, hy2 = 0
            for (let seg = 0; seg < nSeg; seg++) {
                let sum = 0
                const end = (seg + 1) * step
                for (let i = seg * step; i < end; i++) {
                    const xi = x[i]
                    const ax = xi < 0 ? -xi : xi
                    if (ax > peak) peak = ax
                    const sy = s.b[0] * xi + s.b[1] * sx1 + s.b[2] * sx2 - s.a[0] * sy1 - s.a[1] * sy2
                    sx2 = sx1; sx1 = xi; sy2 = sy1; sy1 = sy
                    const hy = sy - 2 * hx1 + hx2 - h.a[0] * hy1 - h.a[1] * hy2
                    hx2 = hx1; hx1 = sy; hy2 = hy1; hy1 = hy
                    sum += hy * hy
                }
                segPower[seg] += sum // channel weight 1.0 for L/R
                if (seg % SEGS_PER_YIELD === SEGS_PER_YIELD - 1) await sleep(0)
            }
        }

        // 400 ms blocks, 75 % overlap = 4 consecutive 100 ms segments
        const lufs = p => -0.691 + 10 * Math.log10(p)
        const blocks = []
        for (let i = 0; i + 4 <= nSeg; i++) {
            blocks.push((segPower[i] + segPower[i + 1] + segPower[i + 2] + segPower[i + 3]) / (4 * step))
        }
        const peakDb = 20 * Math.log10(peak || 1e-9)
        const absGated = blocks.filter(p => lufs(p) > -70)
        if (!absGated.length) return { integrated: -Infinity, samplePeakDb: peakDb }
        const relGate = lufs(absGated.reduce((a, b) => a + b, 0) / absGated.length) - 10
        const gated = absGated.filter(p => lufs(p) > relGate)
        return { integrated: lufs(gated.reduce((a, b) => a + b, 0) / gated.length), samplePeakDb: peakDb }
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

    function getQueueMetas() {
        return getQueueEntities().map(metaOf)
    }

    function getCurrentAudioElement() {
        const mp = getMediaPlayer()
        const el = obsValue(mp?.currentAudioElement) ?? obsValue(mp?.currentMediaPlayer?.currentAudioElement)
        return el instanceof HTMLAudioElement ? el : null
    }

    const srcOf = el => (el && (el.currentSrc || el.src)) || ''

    function getNextEntity() {
        return obsValue(getState()?.queueState?.nextEntity)?.entity ?? null
    }

    // The player stores the get-file-info result on the entity itself. It has the direct file
    // URL even when playback goes through MediaSource (blob: src on the <audio> element).
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

    function resolveUrl(entity, fallbackEl) {
        const di = getDownloadInfo(entity)
        if (di) {
            const r = urlFromDownloadInfo(di)
            if (r.url || di.key) return r
        }
        const src = srcOf(fallbackEl)
        if (src && !src.startsWith('blob:')) return { url: src }
        return { reason: src ? 'аудио идёт через blob/MediaSource' : 'нет ссылки на аудио' }
    }

    // ---------- get-file-info through the client's own media provider ----------

    // The provider signs get-file-info requests with the client's secret; its
    // getFileInfoFromResource() is side-effect free (unlike getMediaSource(), which
    // writes entity.mediaSourceData), so it is safe to call for any track in the queue.
    const FALLBACK_CODECS = ['mp3', 'aac', 'he-aac', 'aac-mp4', 'he-aac-mp4']

    function findMediaProvider() {
        const mp = getMediaPlayer()
        const store = obsValue(getState()?.mediaPlayersStore)
        const candidates = [mp, mp?.currentMediaPlayer, mp?.firstMediaPlayer, mp?.secondMediaPlayer]
        if (store && typeof store === 'object') candidates.push(...Object.values(store))
        for (let c of candidates) {
            for (let depth = 0; depth < 3 && c && typeof c === 'object'; depth++) {
                if (typeof c.getFileInfoFromResource === 'function') return c
                c = c.mediaProvider
            }
        }
        return null
    }

    async function fetchFileInfoUrl(meta) {
        const provider = findMediaProvider()
        if (!provider) throw new Error('media provider не найден')
        const codecs = Array.isArray(provider.codecs) && provider.codecs.length ? provider.codecs : FALLBACK_CODECS
        const res = await provider.getFileInfoFromResource({
            trackId: String(meta.id),
            quality: 'nq',
            codecs,
            transports: ['raw'],
        })
        const di = res?.downloadInfo
        if (!di || typeof di !== 'object') throw new Error('get-file-info: пустой ответ')
        if ('error' in di) throw new Error('get-file-info: ' + String(di.error))
        const r = urlFromDownloadInfo(di)
        if (!r.url) throw new Error(r.reason)
        return r.url
    }

    // ---------- track classification ----------

    const UUID_RE = /^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$/i

    function isUgc(meta) {
        if (!meta) return false
        return meta.trackSource === 'UGC' || meta.trackSource === 'OWN_REPLACED_TO_UGC' || UUID_RE.test(String(meta.id))
    }

    const isOurs = r128 => Boolean(r128 && r128.__audionorm)

    // Catalog r128 from Yandex is never touched; only UGC tracks without r128 or with ours.
    function applyToMeta(meta) {
        if (!isUgc(meta)) return
        if (meta.r128 && !isOurs(meta.r128)) return
        const cached = cache.get(String(meta.id))
        const next = cached
            ? { i: cached.i, tp: cached.tp, __audionorm: 'measured' }
            : { i: PLACEHOLDER.i, tp: PLACEHOLDER.tp, __audionorm: 'placeholder' }
        const cur = meta.r128
        if (cur && cur.i === next.i && cur.tp === next.tp && cur.__audionorm === next.__audionorm) return
        try {
            meta.r128 = next
        } catch (e) {
            warn('cannot write r128 into meta', meta.id, e)
        }
    }

    function applyToQueue() {
        if (!settings.enabled) return
        for (const meta of getQueueMetas()) applyToMeta(meta)
        applyToMeta(metaOf(getCurrentEntity()))
    }

    // ---------- measurement ----------

    const MAX_ATTEMPTS = 3
    const RETRY_COOLDOWN_MS = 5000

    const inflight = new Map() // trackId -> Promise
    const failed = new Map() // trackId -> reason, after MAX_ATTEMPTS (no more retries this session)
    const attempts = new Map() // trackId -> failed attempts so far
    const reasons = new Map() // trackId -> last reason why it is not measured (for the badge)
    const retryAt = new Map() // trackId -> timestamp before which we do not retry
    let chain = Promise.resolve()

    function measureTrack(entity, fallbackEl) {
        const meta = metaOf(entity)
        const id = String(meta.id)
        if (cache.has(id)) return Promise.resolve(cache.get(id))
        if (inflight.has(id)) return inflight.get(id)
        if (failed.has(id)) return Promise.resolve(null)
        if (Date.now() < (retryAt.get(id) ?? 0)) return Promise.resolve(null)

        const expectedMs = Number(meta.durationMs) || 0
        const job = chain.then(async () => {
            const t0 = performance.now()
            // URLs are signed and expire, so resolve right before downloading
            let { url, reason } = resolveUrl(entity, fallbackEl)
            if (!url) {
                try {
                    url = await fetchFileInfoUrl(meta)
                } catch (e) {
                    throw new Error(`${reason}; ${e?.message || e}`)
                }
            }
            const res = await fetch(url)
            if (!res.ok) throw new Error('HTTP ' + res.status)
            const data = await res.arrayBuffer()
            const audio = await new OfflineAudioContext(1, 1, 44100).decodeAudioData(data)
            // Guard against measuring the wrong file (audio element may still point to another track)
            if (expectedMs && Math.abs(audio.duration * 1000 - expectedMs) > DURATION_TOLERANCE_MS) {
                throw new Error(`duration mismatch: ${Math.round(audio.duration * 1000)} vs ${expectedMs} ms`)
            }
            const channels = []
            for (let c = 0; c < Math.min(audio.numberOfChannels, 2); c++) channels.push(audio.getChannelData(c))
            const r = await measureLoudness(channels, audio.sampleRate)
            if (!Number.isFinite(r.integrated)) throw new Error('silent track')
            const value = {
                i: Math.round(r.integrated * 100) / 100,
                tp: Math.round((r.samplePeakDb + TP_MARGIN_DB) * 100) / 100,
            }
            cache.set(id, value)
            saveCache()
            log(`measured "${meta.title}"`, value, `${Math.round(performance.now() - t0)} ms`)
            return value
        })
        const tracked = job
            .catch(e => {
                const reason = e?.message || String(e)
                const n = (attempts.get(id) ?? 0) + 1
                attempts.set(id, n)
                reasons.set(id, reason)
                retryAt.set(id, Date.now() + RETRY_COOLDOWN_MS)
                if (n >= MAX_ATTEMPTS) failed.set(id, reason)
                warn(`measure failed for "${meta.title}" (attempt ${n}/${MAX_ATTEMPTS}):`, reason)
                return null
            })
            .finally(() => {
                inflight.delete(id)
                applyToQueue()
                syncBuiltinGain()
                updateBadge()
            })
        chain = tracked.then(() => undefined)
        inflight.set(id, tracked)
        return tracked
    }

    function needsMeasure(meta) {
        return isUgc(meta) && (!meta.r128 || isOurs(meta.r128)) && !cache.has(String(meta.id))
    }

    function measureCurrentIfNeeded() {
        const entity = getCurrentEntity()
        if (!needsMeasure(metaOf(entity))) return null
        return measureTrack(entity, getCurrentAudioElement())
    }

    // Next track: its mediaSourceData appears once the player preloads it;
    // as a fallback, the preloaded file sits in the other audio element.
    function measureNextIfNeeded() {
        const mp = getMediaPlayer()
        const entity = getNextEntity() ?? mp?.nextContextEntityPair?.entity
        if (!needsMeasure(metaOf(entity))) return
        const currentSrc = srcOf(getCurrentAudioElement())
        const els = Array.isArray(mp?.audioElementsStore) ? mp.audioElementsStore : []
        const other = els.find(el => el instanceof HTMLAudioElement && srcOf(el) && srcOf(el) !== currentSrc)
        measureTrack(entity, getDownloadInfo(entity) ? null : other)
    }

    // ---------- "measure whole playlist" ----------

    // { total, done, ok, failed, cancelled, finishedAt }
    let batch = null
    let lastMeasureQueueValue = null

    function getQueueEntities() {
        const list = obsValue(getState()?.queueState?.entityList)
        if (!Array.isArray(list)) return []
        return list.map(item => item?.entity ?? item).filter(e => metaOf(e))
    }

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
            const value = await measureTrack(entity, null)
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

    // The settings toggle works as a button: every change starts (or cancels) a run.
    function checkBatchTrigger() {
        const v = settings.measureQueue
        if (lastMeasureQueueValue !== null && v !== lastMeasureQueueValue) {
            if (isBatchRunning()) batch.cancelled = true
            else if (settings.enabled) runBatch().catch(e => warn('playlist measure failed', e))
        }
        lastMeasureQueueValue = v
    }

    // ---------- player hook ----------

    let startHook = null // hook of the playback that owns the current queue
    const tappedHooks = new WeakSet()
    const hookOwners = new Map() // hook -> object it was found on
    let appliedKey = null // "<id>|<i>|<tp>" that the built-in r128 gain node currently uses

    function playerRoots() {
        const api = window.pulsesyncApi
        let apiState = null
        try {
            apiState = api?.getState?.()
        } catch {}
        // The wrapper's `state` getter is `this.playbackController.getPlayback().state`,
        // so getPlayback() is the active Sonata Playback that owns `hooks`.
        const playbacks = []
        for (const w of [player, api?.playerInstance]) {
            try {
                const pb = w?.playbackController?.getPlayback?.()
                if (pb) playbacks.push(pb)
            } catch {}
        }
        return [...playbacks, player, api?.playerInstance, window.__pulseSyncPendingPlayerInstance, apiState].filter(
            r => r && typeof r === 'object',
        )
    }

    const HOOK_SEARCH_DEPTH = 6
    const HOOK_SEARCH_MAX_NODES = 4000
    const hookPaths = new Map() // hook -> path where it was found (for the debug report)

    // The Sonata Playback object owns `hooks`, but PulseSync hands out a wrapper
    // (e.g. Ks { playbackController, ... }). Breadth-first search through own properties.
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

    function r128Key(meta) {
        if (!meta) return null
        const r = meta.r128
        return `${meta.id}|${r ? r.i : 'none'}|${r ? r.tp : 'none'}`
    }

    // The built-in normalization only sets the gain in its beforeMediaStartPlaying tap.
    // When our r128 for the playing track changes mid-track, re-run just that tap:
    // it re-reads meta.r128 and calls setR128Gain on the graphs (its fade/smartPreview
    // calls are idempotent for the current entity).
    function syncBuiltinGain() {
        if (!settings.enabled) return
        const meta = metaOf(getCurrentEntity())
        const key = r128Key(meta)
        if (!key || key === appliedKey) return
        const tap = startHook?.taps?.find?.(t => t?.name === 'WebAudioPlugin')
        if (typeof tap?.fn !== 'function') return
        appliedKey = key
        try {
            Promise.resolve(tap.fn()).catch(e => warn('re-apply failed', e))
            log('re-applied built-in r128 gain', meta.r128)
        } catch (e) {
            warn('re-apply failed', e)
        }
    }

    // Called every tick: playbacks can be (re)created, e.g. when switching to My Vibe.
    function installHooks() {
        for (const [hook, owner] of findStartHooks()) {
            hookOwners.set(hook, owner)
            if (tappedHooks.has(hook)) continue
            tappedHooks.add(hook)
            tapStartHook(hook)
        }
        startHook = pickActiveHook()
    }

    function tapStartHook(hook) {
        hook.tapPromise({ name: 'AudioNorm', stage: HOOK_STAGE }, async () => {
            // Must never throw: a rejected tap could break playback start.
            try {
                settings = readSettings()
                if (!settings.enabled) return
                const meta = metaOf(getCurrentEntity())
                if (isUgc(meta)) {
                    applyToMeta(meta)
                    if (needsMeasure(meta) && settings.maxWaitMs > 0) {
                        const p = measureCurrentIfNeeded()
                        if (p) {
                            await Promise.race([p, sleep(settings.maxWaitMs)])
                            applyToMeta(meta)
                        }
                    }
                }
                // WebAudioPlugin runs right after us with exactly this r128
                if (!startHook || hook === startHook) appliedKey = r128Key(meta)
            } catch (e) {
                warn('hook error', e)
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

        const { text, problem } = computeStatus()
        if (!problem) problemSince = 0
        else if (!problemSince) problemSince = Date.now()
        const show = settings.debug && problem && Date.now() - problemSince >= PROBLEM_SHOW_DELAY_MS
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

    function waitForPlayer() {
        const api = window.pulsesyncApi
        if (typeof api?._waitForPlayer !== 'function') return Promise.resolve(null)
        const wait = new Promise(resolve => {
            try {
                api._waitForPlayer(p => resolve(p ?? null))
            } catch {
                resolve(null)
            }
        })
        return Promise.race([wait, sleep(15000).then(() => null)])
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
        const src = srcOf(el)
        return {
            version: '0.4.0',
            settings,
            builtinR128: builtinNormalizationEnabled(),
            status: computeStatus().text,
            mediaProviderFound: !!findMediaProvider(),
            batch,
            queueLength: getQueueEntities().length,
            player: describe(player),
            playerInstance: describe(api?.playerInstance),
            playerInstanceIsPlayer: api?.playerInstance === player,
            pendingPlayerInstance: describe(window.__pulseSyncPendingPlayerInstance),
            sonataStateIsPlayerState: !!player?.state && player.state === window.sonataState,
            playbackController: describe(player?.playbackController),
            playbackControllerChildren: (() => {
                const pc = player?.playbackController
                if (!pc || typeof pc !== 'object') return null
                const out = {}
                for (const k of Object.keys(pc).slice(0, 30)) {
                    try {
                        const v = pc[k]
                        out[k] = v && typeof v === 'object' ? describe(v).own.slice(0, 25) : typeof v
                    } catch {}
                }
                return out
            })(),
            hooksFound: hookOwners.size,
            hookPaths: Array.from(hookPaths.values()),
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

        installHooks()
        applyToQueue()
        lastMeasureQueueValue = settings.measureQueue // do not start a run on load

        try {
            window.pulsesyncApi?.getSettings?.(ADDON_NAME)?.onChange?.(() => {
                settings = readSettings()
                checkBatchTrigger()
                applyToQueue()
                updateBadge()
            })
        } catch {}

        let lastId = null
        let lastIdChangedAt = 0
        let tick = 0
        setInterval(() => {
            settings = readSettings()
            checkBatchTrigger()
            // the search walks object graphs: every second until found, then every 10 s
            if (!startHook || ++tick % 10 === 0) installHooks()
            if (settings.enabled) {
                applyToQueue()
                const id = String(metaOf(getCurrentEntity())?.id ?? '')
                if (id !== lastId) {
                    lastId = id
                    lastIdChangedAt = Date.now()
                }
                // give the audio element a moment to switch src; retried every tick with cooldown
                if (Date.now() - lastIdChangedAt > 1500) measureCurrentIfNeeded()
                measureNextIfNeeded()
                syncBuiltinGain()
            }
            updateBadge()
        }, 1000)

        log('started', { cached: cache.size, settings, builtinR128: builtinNormalizationEnabled() })
    }

    // Debug helpers in DevTools: __audionorm.status(), __audionorm.clearCache()
    window.__audionorm = {
        cache,
        failed,
        reasons,
        status: debugReport,
        clearCache() {
            cache.clear()
            failed.clear()
            attempts.clear()
            reasons.clear()
            retryAt.clear()
            saveCache()
        },
    }

    start().catch(e => console.error(TAG, 'start failed', e))
})()
