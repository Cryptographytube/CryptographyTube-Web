/*!
 * mini-key-engine.js — chain-aware Casascius mini-key browser for /mini-key/<chain>.html
 *
 * Generalises the standalone Bitcoin mini-key engine to EVERY supported chain.
 * A Casascius mini key is 'S' + (L-1) Base58 chars; the private key is simply
 * SHA256(miniKeyString) — a plain 32-byte scalar that is a valid key on every
 * chain (secp256k1 for BTC/EVM/XRP/LTC/…; ed25519 seed for SOL/TON/SUI).
 *
 * The page's chain is read from window.CGT_CONFIG (chain + chainInfo). Per-chain
 * address derivation reuses the shared window.CryptoUtils encoders (identical
 * output to /brainwallet/ and /private-keys/) and balances come from the shared
 * window.BalanceChecker.fetch*BalancesBatch methods. Bitcoin keeps its own
 * self-tested P2PKH path and its 4 address-type selector; every other chain
 * renders one canonical address per key.
 *
 * Loaded with `defer` AFTER CGT_CONFIG + app.obf.js so CryptoUtils/BalanceChecker
 * exist; it still polls for the noble crypto modules (loaded as ESM).
 */
(function () {
    'use strict';

    var B58 = '123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz';
    var MK_PER_PAGE = 60;
    var L = 30;
    var curStart = 0n;
    var fillToken = 0;
    var ADDR_TYPE = 'legacy';                 // bitcoin only
    var TYPE_META = { legacy: 1, segwit: 1, script: 1, taproot: 1 };
    var BASE = window.location.pathname;
    var _enc = new TextEncoder();

    var CFG = window.CGT_CONFIG || {};
    var CHAIN = CFG.chain || 'bitcoin';
    var CINFO = CFG.chainInfo || {};
    var CTYPE = CINFO.type || 'bitcoin';
    var SYM = CINFO.symbol || 'BTC';
    var EXP = CINFO.explorer || '';
    var IS_BTC = (CHAIN === 'bitcoin');
    var DECIMALS_SHOWN = IS_BTC ? 8 : 8;      // summary decimals

    /* --------------------------------------------------- keyspace (BigInt) --- */
    function pow58(e) { var r = 1n; for (var i = 0; i < e; i++) r *= 58n; return r; }
    var _maxCache = {};
    function maxIdx() { if (_maxCache[L] == null) _maxCache[L] = pow58(L - 1) - 1n; return _maxCache[L]; }
    function lastStart() { var pn = BigInt(MK_PER_PAGE); return (maxIdx() / pn) * pn; }
    function pageStart(idx) {
        var pn = BigInt(MK_PER_PAGE);
        if (idx < 0n) idx = 0n;
        var m = maxIdx();
        if (idx > m) idx = m;
        return (idx / pn) * pn;
    }

    /* ------------------------------------------------------- number format --- */
    function comma(n) { return n.toString().replace(/\B(?=(\d{3})+(?!\d))/g, ','); }
    function sci(n) {
        var s = n.toString();
        if (s.length <= 6) return s;
        var exp = s.length - 1;
        var d3 = s.slice(0, 3);
        var round = s.length > 3 && s.charCodeAt(3) >= 53;
        var num = parseInt(d3, 10) + (round ? 1 : 0);
        if (num >= 1000) { num = Math.floor(num / 10); exp++; }
        var ns = String(num);
        return ns[0] + '.' + ns.slice(1) + 'E+' + exp;
    }
    function formatOrdinal(n) { return n.toString().length > 15 ? sci(n) : comma(n); }
    function fmtAmt(n) {
        if (!isFinite(n)) n = 0;
        if (n === 0) return '0';
        var s = n.toFixed(DECIMALS_SHOWN);
        if (s.indexOf('.') !== -1) s = s.replace(/\.?0+$/, '');
        return s || '0';
    }

    /* ---------------------------------------------------- crypto (noble) --- */
    function S256(b) { return window.NobleHashes.sha256Module.sha256(b); }
    function RMD(b) { return window.NobleHashes.ripemd160Module.ripemd160(b); }
    function PUB(priv, c) { return window.NobleCurves.secp256k1Module.secp256k1.getPublicKey(priv, c); }
    function bytesToHex(b) { var h = ''; for (var i = 0; i < b.length; i++) h += (b[i] >>> 4).toString(16) + (b[i] & 15).toString(16); return h; }
    function b58enc(bytes) {
        var zeros = 0; while (zeros < bytes.length && bytes[zeros] === 0) zeros++;
        var num = 0n; for (var i = 0; i < bytes.length; i++) num = num * 256n + BigInt(bytes[i]);
        var out = ''; while (num > 0n) { out = B58[Number(num % 58n)] + out; num = num / 58n; }
        for (var z = 0; z < zeros; z++) out = '1' + out;
        return out;
    }
    function b58check(payload) {
        var chk = S256(S256(payload)).slice(0, 4);
        var full = new Uint8Array(payload.length + 4);
        full.set(payload, 0); full.set(chk, payload.length);
        return b58enc(full);
    }
    function wifFrom(priv, c) {
        var payload;
        if (c) { payload = new Uint8Array(34); payload[0] = 0x80; payload.set(priv, 1); payload[33] = 0x01; }
        else { payload = new Uint8Array(33); payload[0] = 0x80; payload.set(priv, 1); }
        return b58check(payload);
    }
    function p2pkh(pub) {
        var h = RMD(S256(pub));
        var payload = new Uint8Array(21); payload[0] = 0x00; payload.set(h, 1);
        return b58check(payload);
    }
    function indexToMiniKey(idx, len) {
        var free = len - 1, n = idx, s = '';
        while (n > 0n) { s = B58[Number(n % 58n)] + s; n = n / 58n; }
        while (s.length < free) s = '1' + s;
        return 'S' + s;
    }
    function minikeyToPriv(mk) { return S256(_enc.encode(mk)); }

    /* --------------------------------------------------- monero (XMR) --- */
    // Real Monero standard-address derivation, ported from monero-derive.js so
    // the mini-key engine stays self-contained (no CGT/private-keys hooks). The
    // page already imports keccak-256 (sha3) + ed25519 as ESM. Each row's scalar
    // is the same big-endian key N used by every chain:
    //   spend = N mod L ; view = keccak(LE(spend)) mod L
    //   address = base58Monero(0x12 ‖ spend·G ‖ view·G ‖ keccak(prefix‖pubs)[:4])
    var XMR_B58 = '123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz';
    var XMR_ENC = [0, 2, 3, 5, 6, 7, 9, 10, 11];      // base58 len for a 0..8-byte block
    var _xmrInit = false, _xmrKeccak, _xmrPT, _xmrL, _xmrCache = {};
    function xmrReady() {
        return !!(window.NobleHashes && window.NobleHashes.sha3Module && window.NobleHashes.sha3Module.keccak_256 &&
                  window.NobleCurves && window.NobleCurves.ed25519Module && window.NobleCurves.ed25519Module.ed25519);
    }
    function xmrInit() {
        if (_xmrInit) return;
        _xmrKeccak = window.NobleHashes.sha3Module.keccak_256;
        var ed = window.NobleCurves.ed25519Module.ed25519;
        _xmrPT = ed.ExtendedPoint || ed.Point;        // noble exposes ExtendedPoint
        _xmrL = ed.CURVE.n;                            // ed25519 group order
        _xmrInit = true;
    }
    function _xmrLeToScalar(b) { var n = 0n; for (var i = b.length - 1; i >= 0; i--) n = (n << 8n) | BigInt(b[i]); return n % _xmrL; }
    function _xmrScalarToLe(n) { n = ((n % _xmrL) + _xmrL) % _xmrL; var b = new Uint8Array(32); for (var i = 0; i < 32; i++) { b[i] = Number(n & 255n); n >>= 8n; } return b; }
    function _xmrPubFromScalar(n) { n = ((n % _xmrL) + _xmrL) % _xmrL; return _xmrPT.BASE.multiply(n === 0n ? _xmrL : n).toRawBytes(); }
    function _xmrConcat() { var a = [].slice.call(arguments), len = 0, i; for (i = 0; i < a.length; i++) len += a[i].length; var r = new Uint8Array(len), o = 0; for (i = 0; i < a.length; i++) { r.set(a[i], o); o += a[i].length; } return r; }
    function _xmrEncBlock(bytes) { var num = 0n, i; for (i = 0; i < bytes.length; i++) num = (num << 8n) | BigInt(bytes[i]); var outLen = XMR_ENC[bytes.length], s = '', t = num; while (t > 0n) { s = XMR_B58[Number(t % 58n)] + s; t /= 58n; } while (s.length < outLen) s = '1' + s; return s; }
    function _xmrB58(bytes) { var o = ''; for (var i = 0; i < bytes.length; i += 8) o += _xmrEncBlock(bytes.slice(i, i + 8)); return o; }
    function xmrDerive(privHex) {
        if (_xmrCache[privHex]) return _xmrCache[privHex];
        xmrInit();
        var beHex = (privHex || '').replace(/^0x/, '').replace(/[^0-9a-fA-F]/g, '') || '0';
        var spendScalar = BigInt('0x' + beHex) % _xmrL;
        var secSpend = _xmrScalarToLe(spendScalar);
        var viewScalar = _xmrLeToScalar(_xmrKeccak(secSpend));
        var data = _xmrConcat(new Uint8Array([0x12]), _xmrPubFromScalar(spendScalar), _xmrPubFromScalar(viewScalar));
        var checksum = _xmrKeccak(data).slice(0, 4);
        var r = { address: _xmrB58(_xmrConcat(data, checksum)), viewKey: bytesToHex(_xmrScalarToLe(viewScalar)) };
        _xmrCache[privHex] = r;
        return r;
    }

    /* ------------------------------------------------- per-chain address --- */
    function CU() { return window.CryptoUtils; }
    function loadingAddr(a) { return !a || a === 'Loading...' || a === 'Error'; }

    // WIF/secret labels shown in the key column for this chain.
    function wifLabels() {
        if (IS_BTC) return ['WIF(c)', 'WIF(u)'];
        if (CTYPE === 'litecoin' || CTYPE === 'dogecoin' || CTYPE === 'zcash' || CTYPE === 'bitcoincash') return ['WIF'];
        if (CTYPE === 'xrp') return ['Secret'];
        return [];
    }
    // Returns [{label,value}] matching wifLabels() order (or fewer on error).
    function wifsFor(priv, privHex) {
        try {
            if (IS_BTC) return [{ label: 'WIF(c)', value: wifFrom(priv, true) }, { label: 'WIF(u)', value: wifFrom(priv, false) }];
            var cu = CU(); if (!cu) return [];
            if (CTYPE === 'litecoin') return [{ label: 'WIF', value: cu.hexToLitecoinWif(privHex) }];
            if (CTYPE === 'dogecoin') return [{ label: 'WIF', value: cu.hexToDogecoinWif(privHex) }];
            if (CTYPE === 'zcash') return [{ label: 'WIF', value: cu.hexToZcashWif(privHex) }];
            if (CTYPE === 'bitcoincash') return [{ label: 'WIF', value: cu.hexToWif(privHex) }];
            if (CTYPE === 'xrp') return [{ label: 'Secret', value: cu.xrpSecretFromHex ? cu.xrpSecretFromHex(privHex) : (cu.hexToXrpSecret ? cu.hexToXrpSecret(privHex) : '') }];
        } catch (e) {}
        return [];
    }

    // Returns [{label, addr}] for this chain. Bitcoin keeps the 4-type logic.
    function addrsFor(priv, privHex) {
        if (CTYPE === 'monero') return [{ label: '', addr: xmrDerive(privHex).address }];
        var cu = CU();
        if (IS_BTC) {
            if (ADDR_TYPE === 'legacy') {
                return [{ label: '(c)', addr: p2pkh(PUB(priv, true)) },
                        { label: '(u)', addr: p2pkh(PUB(priv, false)) }];
            }
            var pubHex = bytesToHex(PUB(priv, true)), a = '';
            try {
                if (ADDR_TYPE === 'segwit') a = cu.toBitcoinSegWit(pubHex);
                else if (ADDR_TYPE === 'script') a = cu.toBitcoinScript(pubHex);
                else if (ADDR_TYPE === 'taproot') a = cu.toBitcoinTaproot(privHex);
            } catch (e) { a = ''; }
            return [{ label: '', addr: a }];
        }
        if (!cu) return [{ label: '', addr: 'Loading...' }];
        var out = '';
        try {
            switch (CTYPE) {
                case 'evm':         out = cu.toEVMAddress(privHex); break;
                case 'solana':      out = cu.toSolanaAddress(privHex); break;
                case 'tron':        out = cu.toTronAddress(privHex); break;
                case 'usdt':        out = cu.toTronAddress(privHex); break;   // USDT shown on its Tron host
                case 'xrp':         out = cu.toXrpAddress(privHex); break;
                case 'sui':         out = cu.toSuiAddress(privHex); break;
                case 'litecoin':    out = cu.toLitecoinAddress(privHex, 'legacy'); break;
                case 'dogecoin':    out = cu.toDogecoinAddress(privHex, 'legacy'); break;
                case 'bitcoincash': out = cu.toBitcoinCashAddress(privHex, 'cashaddr'); break;
                case 'zcash':       out = cu.toZcashAddress(privHex, 'p2pkh'); break;
                case 'ton':
                    var t = cu.toTonAddresses(privHex, 'v4');
                    out = (t && (t.nonBounceable || t.bounceable)) || '';
                    break;
                default:            out = cu.toEVMAddress(privHex); break;
            }
        } catch (e) { out = ''; }
        return [{ label: '', addr: out }];
    }

    // Does this chain have everything it needs to derive right now?
    function specReady() {
        if (IS_BTC && ADDR_TYPE === 'legacy') return true;          // own P2PKH, no CryptoUtils
        if (CTYPE === 'monero') return xmrReady();                  // own derivation via noble sha3+ed25519
        var cu = CU();
        if (!cu) return false;
        var map = {
            evm: 'toEVMAddress', usdt: 'toTronAddress', solana: 'toSolanaAddress', tron: 'toTronAddress',
            xrp: 'toXrpAddress', sui: 'toSuiAddress', litecoin: 'toLitecoinAddress', dogecoin: 'toDogecoinAddress',
            bitcoincash: 'toBitcoinCashAddress', zcash: 'toZcashAddress', ton: 'toTonAddresses'
        };
        if (IS_BTC) return typeof cu.toBitcoinSegWit === 'function' && typeof cu.toBitcoinScript === 'function' && typeof cu.toBitcoinTaproot === 'function';
        var fn = map[CTYPE] || 'toEVMAddress';
        return typeof cu[fn] === 'function';
    }

    function explorerHref(addr) { return EXP ? (EXP + addr) : ''; }
    function addrItemHtml(label, addr, idx) {
        var href = addr ? explorerHref(addr) : '';
        var inner = addr
            ? '<a class="address-link mk-addr" data-ai="' + idx + '" target="_blank" rel="nofollow noopener"' + (href ? ' href="' + href + '"' : '') + '>' + addr + '</a>'
            : '<a class="address-link mk-addr" data-ai="' + idx + '">&mdash;</a>';
        return '<span class="address-item">' + (label ? label + ' ' : '') + inner + '</span>';
    }

    /* --------------------------------------------------- wait for noble --- */
    function whenNoble(cb) {
        function ready() {
            return window.NobleCurves && window.NobleCurves.secp256k1Module &&
                   window.NobleHashes && window.NobleHashes.sha256Module && window.NobleHashes.ripemd160Module;
        }
        if (ready()) return cb();
        var done = false, iv;
        function go() {
            if (done || !ready()) return;
            done = true; clearInterval(iv); window.removeEventListener('noble-loaded', go);
            cb();
        }
        window.addEventListener('noble-loaded', go);
        iv = setInterval(go, 40);
    }

    /* ------------------------------------------------------- clipboard --- */
    function MK_copy(text) {
        if (!text || text === '—') return;
        try { navigator.clipboard.writeText(text); }
        catch (e) {
            try { var ta = document.createElement('textarea'); ta.value = text; document.body.appendChild(ta); ta.select(); document.execCommand('copy'); document.body.removeChild(ta); } catch (_) {}
        }
    }
    window.MK_copy = MK_copy;

    function spinner() { return '<img src="../assets/svgs/solid/spinner.svg" class="fa-icon fa-spin" width="14" height="14" alt="">'; }

    /* ---------------------------------------------- render one mini-key row --- */
    function cardSkeleton(ordinal, mk) {
        var sp = spinner();
        var icon = '<img src="../assets/svgs/regular/copy.svg" class="fa-icon " width="12" height="12" alt="">';
        var mkAttr = String(mk).replace(/"/g, '&quot;');
        var wifHtml = '';
        var labels = wifLabels();
        for (var w = 0; w < labels.length; w++) {
            wifHtml +=
                '<div class="key-wif">' +
                    '<span class="key-label">' + labels[w] + '</span>' +
                    '<a class="wif-value key-link mk-wif" data-wi="' + w + '" rel="nofollow">' + sp + '</a>' +
                    '<button class="copy-btn mk-copy-wif" data-wi="' + w + '" data-copy="" title="Copy">' + icon + '</button>' +
                '</div>';
        }
        return '' +
        '<div class="key-row" data-index="' + ordinal + '">' +
            '<div class="col-key">' +
                '<div class="key-hex">' +
                    '<span class="key-label">HEX</span>' +
                    '<a class="private-key key-link mk-priv" rel="nofollow">' + sp + '</a>' +
                    '<button class="copy-btn mk-copy-priv" data-copy="" title="Copy HEX">' + icon + '</button>' +
                '</div>' +
                '<div class="key-passphrase">' +
                    '<span class="key-label">Mini Key</span>' +
                    '<span class="passphrase-text">' + mk + '</span>' +
                    '<button class="copy-btn" data-copy="' + mkAttr + '" title="Copy Mini Key">' + icon + '</button>' +
                '</div>' +
                wifHtml +
            '</div>' +
            '<div class="col-address">' +
                '<span class="address-item"><a class="address-link mk-addr" target="_blank" rel="nofollow noopener">' + sp + '</a></span>' +
            '</div>' +
            '<div class="col-balance">' +
                '<span class="mk-bal">' + sp + '</span>' +
            '</div>' +
        '</div>';
    }

    function setCopyBtn(card, sel, val) { var el = card.querySelector(sel); if (el) el.setAttribute('data-copy', val == null ? '' : val); }
    function setPriv(card, hex) {
        var el = card.querySelector('.mk-priv'); if (!el) return;
        el.textContent = hex;
        if (hex && hex !== '—') el.setAttribute('href', '../key.html?k=' + hex); else el.removeAttribute('href');
    }

    /* ------------------------------- derive WIF + addresses, then balances --- */
    function deriveAndFill(token) {
        whenNoble(function () {
            if (token !== fillToken) return;
            if (!specReady()) { return setTimeout(function () { deriveAndFill(token); }, 120); }
            var cont = document.getElementById('keysContainer'); if (!cont) return;
            var cards = cont.querySelectorAll('.key-row');
            var addrs = [], anyLoading = false;
            for (var i = 0; i < cards.length; i++) {
                var card = cards[i];
                var mk = indexToMiniKey(curStart + BigInt(i), L);
                var privHex = '—', items = [], wifs = [];
                try {
                    var priv = minikeyToPriv(mk);
                    privHex = bytesToHex(priv);
                    wifs = wifsFor(priv, privHex);
                    items = addrsFor(priv, privHex);
                } catch (e) { privHex = '—'; items = []; }
                var wifHref = (privHex !== '—') ? '../key.html?k=' + privHex : null;
                setPriv(card, privHex); setCopyBtn(card, '.mk-copy-priv', privHex);
                var wifEls = card.querySelectorAll('.mk-wif');
                for (var w = 0; w < wifEls.length; w++) {
                    var val = (wifs[w] && wifs[w].value) ? wifs[w].value : '—';
                    wifEls[w].textContent = val;
                    if (val && val !== '—' && wifHref) wifEls[w].setAttribute('href', wifHref); else wifEls[w].removeAttribute('href');
                }
                var cbtns = card.querySelectorAll('.mk-copy-wif');
                for (var c = 0; c < cbtns.length; c++) { cbtns[c].setAttribute('data-copy', (wifs[c] && wifs[c].value) ? wifs[c].value : ''); }
                var aHtml = '', bHtml = '';
                for (var k = 0; k < items.length; k++) {
                    if (loadingAddr(items[k].addr)) anyLoading = true;
                    aHtml += addrItemHtml(items[k].label, items[k].addr, k);
                    bHtml += '<span class="mk-bal" data-ai="' + k + '">' + spinner() + '</span>';
                    if (items[k].addr && !loadingAddr(items[k].addr)) addrs.push(items[k].addr);
                }
                var ae = card.querySelector('.col-address'); if (ae) ae.innerHTML = aHtml;
                var be = card.querySelector('.col-balance'); if (be) be.innerHTML = bHtml;
            }
            if (anyLoading) { return setTimeout(function () { deriveAndFill(token); }, 150); }  // encoders still booting
            fetchBalances(addrs, token);
        });
    }

    function renderBal(el, val) {
        if (!el) return;
        val = val || {};
        var bs = (val.balanceStr != null) ? val.balanceStr : '0';
        var sym = val.symbol || SYM;
        var balNum = parseFloat(bs) || 0;
        if (balNum > 0) el.innerHTML = '<span class="balance-value">' + bs + ' ' + sym + '</span>';
        else el.innerHTML = '<span class="balance-empty">0 ' + sym + '</span>';
    }

    function updateSummary(bal, recv, tx) {
        var b = document.getElementById('totalBalance'); if (b) b.textContent = fmtAmt(bal) + ' ' + SYM;
        var r = document.getElementById('totalReceived'); if (r) r.textContent = fmtAmt(recv) + ' ' + SYM;
        var t = document.getElementById('totalTx'); if (t) t.textContent = String(tx);
    }

    // Resolve the right BalanceChecker call for this chain -> Promise<Map>.
    function balancePromise(addrs) {
        var BCh = window.BalanceChecker;
        if (CTYPE === 'usdt') {
            var TOK = window.CGT_USDT_TOKEN;
            if (!TOK || typeof TOK.fetchTrc20 !== 'function') return null;
            return TOK.fetchTrc20(addrs).then(function (m) {
                var out = new Map();
                m.forEach(function (v, k) {
                    var num = TOK.fmt ? TOK.fmt(v) : String(v);
                    out.set(k, { balanceStr: num, symbol: 'USDT', received: '0', txCount: 0, active: (v && v > 0n) });
                });
                return out;
            });
        }
        if (CTYPE === 'monero') return Promise.resolve(new Map());  // no public per-address XMR balance API → shows 0 XMR
        if (!BCh) return null;
        switch (CTYPE) {
            case 'bitcoin':     return typeof BCh.fetchBitcoinBalancesBatch === 'function' ? BCh.fetchBitcoinBalancesBatch(addrs) : null;
            case 'evm':         return typeof BCh.fetchEvmBalancesBatch === 'function' ? BCh.fetchEvmBalancesBatch(addrs, CHAIN) : null;
            case 'solana':      return typeof BCh.fetchSolanaBalancesBatch === 'function' ? BCh.fetchSolanaBalancesBatch(addrs) : null;
            case 'tron':        return typeof BCh.fetchTronBalancesBatch === 'function' ? BCh.fetchTronBalancesBatch(addrs) : null;
            case 'xrp':         return typeof BCh.fetchXrpBalancesBatch === 'function' ? BCh.fetchXrpBalancesBatch(addrs) : null;
            case 'sui':         return typeof BCh.fetchSuiBalancesBatch === 'function' ? BCh.fetchSuiBalancesBatch(addrs) : null;
            case 'ton':         return typeof BCh.fetchTonBalancesBatch === 'function' ? BCh.fetchTonBalancesBatch(addrs) : null;
            case 'litecoin':    return typeof BCh.fetchLitecoinBalancesBatch === 'function' ? BCh.fetchLitecoinBalancesBatch(addrs) : null;
            case 'dogecoin':    return typeof BCh.fetchDogecoinBalancesBatch === 'function' ? BCh.fetchDogecoinBalancesBatch(addrs) : null;
            case 'bitcoincash': return typeof BCh.fetchBitcoinCashBalancesBatch === 'function' ? BCh.fetchBitcoinCashBalancesBatch(addrs) : null;
            case 'zcash':       return typeof BCh.fetchZcashBalancesBatch === 'function' ? BCh.fetchZcashBalancesBatch(addrs) : null;
            default:            return typeof BCh.fetchEvmBalancesBatch === 'function' ? BCh.fetchEvmBalancesBatch(addrs, CHAIN) : null;
        }
    }

    function fetchBalances(addrs, token) {
        if (token !== fillToken) return;
        if (!addrs.length) { updateSummary(0, 0, 0); return; }
        var p = balancePromise(addrs);
        if (!p) { return setTimeout(function () { fetchBalances(addrs, token); }, 150); } // await deferred libs
        p.then(function (map) {
            if (token !== fillToken) return;
            if (!map) map = new Map();
            var cont = document.getElementById('keysContainer'); if (!cont) return;
            var cards = cont.querySelectorAll('.key-row');
            var sumBal = 0, sumRecv = 0, sumTx = 0;
            for (var i = 0; i < cards.length; i++) {
                var links = cards[i].querySelectorAll('.mk-addr');
                var bals = cards[i].querySelectorAll('.mk-bal');
                var rowBal = 0, rowActive = false;
                for (var j = 0; j < links.length; j++) {
                    var addr = links[j].textContent;
                    var v = (addr && addr !== '—') ? (map.get(addr) || {}) : {};
                    renderBal(bals[j], v);
                    // EVM balances come back unit-switched (POL / Gwei / Wei) for readability;
                    // normalise to the main unit before summing so the total isn't inflated.
                    var vsym = v.symbol || SYM;
                    var mult = (vsym === 'Gwei') ? 1e-9 : (vsym === 'Wei') ? 1e-18 : 1;
                    var b = (parseFloat(v.balanceStr) || 0) * mult;
                    rowBal += b; rowActive = rowActive || !!v.active || (v.status > 0);
                    sumBal += b;
                    sumRecv += (parseFloat(v.received) || 0) * mult;
                    sumTx += parseInt(v.txCount, 10) || 0;
                }
                cards[i].classList.toggle('has-balance', rowBal > 0);
                cards[i].classList.toggle('was-active', rowBal <= 0 && rowActive);
            }
            updateSummary(sumBal, sumRecv, sumTx);
        }).catch(function () {});
    }

    /* ----------------------------------------------------------- navigation --- */
    function makeUrl(start) { return BASE + '?len=' + L + '&i=' + (start + 1n).toString() + (IS_BTC ? '&type=' + ADDR_TYPE : ''); }
    function bindNav(ids, target) {
        ids.forEach(function (id) {
            var el = document.getElementById(id); if (!el) return;
            el.href = makeUrl(target);
            el.onclick = function (e) {
                if (e.button !== 0 || e.metaKey || e.ctrlKey || e.shiftKey || e.altKey) return;
                e.preventDefault(); goTo(target);
            };
        });
    }
    function updateNav() {
        var pn = BigInt(MK_PER_PAGE), last = lastStart();
        var prev = curStart > 0n ? curStart - pn : 0n;
        var next = curStart + pn; if (next > last) next = last;
        bindNav(['btn-first', 'btn-first-bottom'], 0n);
        bindNav(['btn-prev', 'btn-prev-bottom'], prev);
        bindNav(['btn-next', 'btn-next-bottom'], next);
        bindNav(['btn-last', 'btn-last-bottom'], last);
        ['btn-random', 'btn-random-bottom'].forEach(function (id) {
            var el = document.getElementById(id); if (!el) return;
            el.removeAttribute('href'); el.style.cursor = 'pointer';
            el.onclick = function (e) { e.preventDefault(); goTo(randomStart()); };
        });
        ['btn-prev', 'btn-prev-bottom'].forEach(function (id) {
            var el = document.getElementById(id); if (!el) return;
            var off = curStart <= 0n; el.style.opacity = off ? '0.4' : ''; el.style.pointerEvents = off ? 'none' : '';
        });
        ['btn-next', 'btn-next-bottom', 'btn-last', 'btn-last-bottom'].forEach(function (id) {
            var el = document.getElementById(id); if (!el) return;
            var off = curStart >= last; el.style.opacity = off ? '0.4' : ''; el.style.pointerEvents = off ? 'none' : '';
        });
    }
    function randomStart() {
        var total = maxIdx() + 1n;
        var nbytes = Math.ceil(total.toString(2).length / 8) + 4;
        var rb = new Uint8Array(nbytes); crypto.getRandomValues(rb);
        var n = 0n; for (var i = 0; i < rb.length; i++) n = (n << 8n) | BigInt(rb[i]);
        return pageStart(n % total);
    }

    function updatePageInfo() {
        var ord = curStart + 1n;
        var pageNum = document.getElementById('cgt-page-num'); if (pageNum) pageNum.textContent = '#' + formatOrdinal(ord);
        var totEl = document.getElementById('cgt-total-num'); if (totEl) totEl.textContent = '#' + sci(maxIdx() + 1n);
        var total = maxIdx() + 1n;
        var pct = total > 0n ? Number(curStart * 1000000n / total) / 10000 : 0;
        var bar = document.getElementById('cgt-progress-bar'); var txt = document.getElementById('cgt-progress-text');
        if (bar) bar.style.width = Math.max(pct, 0.00001) + '%';
        if (txt) txt.textContent = pct.toFixed(8) + '%';
        var input = document.getElementById('pageInput'); if (input) input.value = ord.toString();
        if (window.CGT_CONFIG) window.CGT_CONFIG.page = ord.toString();
    }

    /* --------------------------------------------------------- page render --- */
    function renderPage(start, skipPush) {
        curStart = pageStart(start);
        var cont = document.getElementById('keysContainer'); if (!cont) return;
        var html = '', m = maxIdx();
        for (var i = 0; i < MK_PER_PAGE; i++) {
            var idx = curStart + BigInt(i);
            if (idx > m) break;
            html += cardSkeleton(idx + 1n, indexToMiniKey(idx, L));
        }
        cont.innerHTML = html;
        ['totalBalance', 'totalReceived', 'totalTx'].forEach(function (id) { var el = document.getElementById(id); if (el) el.innerHTML = spinner(); });
        updateNav(); updatePageInfo();
        if (!skipPush) { try { window.history.pushState({ mkStart: curStart.toString(), len: L }, '', makeUrl(curStart)); } catch (e) {} }
        deriveAndFill(++fillToken);
    }
    function goTo(start) { renderPage(start, false); }

    /* ------------------------------------------------- format switch 22/30 --- */
    function setActiveFormatCard() {
        document.querySelectorAll('#formatCards .address-type-card').forEach(function (c) {
            c.classList.toggle('active', parseInt(c.getAttribute('data-len'), 10) === L);
        });
    }
    window.MK_setFormat = function (len) {
        if (len !== 22 && len !== 30) return;
        L = len; setActiveFormatCard(); goTo(0n);
    };

    /* ------------------------------- bitcoin address-type switch (btc only) --- */
    function setActiveTypeCard() {
        document.querySelectorAll('#addressTypeCards .address-type-card').forEach(function (c) {
            c.classList.toggle('active', c.getAttribute('data-type') === ADDR_TYPE);
        });
    }
    window.MK_setType = function (t) {
        if (!IS_BTC || !TYPE_META[t]) return;
        ADDR_TYPE = t; setActiveTypeCard();
        if (window.CGT_CONFIG) window.CGT_CONFIG.type = t;
        try { window.history.replaceState(window.history.state, '', makeUrl(curStart)); } catch (e) {}
        deriveAndFill(++fillToken);
    };

    /* ------------------------------------------------------- jump (Mini #) --- */
    window.MK_jump = function () {
        var input = document.getElementById('pageInput');
        var raw = input ? String(input.value || '').replace(/[ ,]/g, '').trim() : '';
        var ord; try { ord = BigInt(raw); } catch (e) { ord = 1n; }
        if (ord < 1n) ord = 1n;
        goTo(pageStart(ord - 1n));
    };

    /* ----------------------------------------------- bitcoin self-test only --- */
    function selfTest() {
        if (!IS_BTC) return;
        whenNoble(function () {
            try {
                var p = new Uint8Array(32); p[31] = 1;
                var ok = wifFrom(p, true) === 'KwDiBf89QgGbjEhKnhXJuH7LrciVrZi3qYjgd9M7rFU73sVHnoWn' &&
                         p2pkh(PUB(p, true)) === '1BgGZ9tcN4rm9KBzDn7KprQz87SZ26SAMH';
                console.log(ok ? '[mini-key] self-test ok' : '[mini-key] self-test FAILED');
            } catch (e) { console.warn('[mini-key] self-test error', e); }
        });
    }

    /* ---------------------------------- per-chain static UI (labels/symbols) --- */
    function applyChainUi() {
        // Balance-summary + keys-header symbols (initial text; refreshed on render).
        ['totalBalance', 'totalReceived'].forEach(function (id) { var el = document.getElementById(id); if (el && /^\s*0\b/.test(el.textContent)) el.textContent = '0 ' + SYM; });
        // Hide the Bitcoin-only address-type selector on non-bitcoin chains.
        if (!IS_BTC) {
            var sel = document.getElementById('addressTypeCards');
            if (sel) { var wrap = sel.closest ? sel.closest('.address-type-selector') : sel.parentNode; if (wrap) wrap.style.display = 'none'; }
        }
    }

    /* ------------------------------------------------------------------ init --- */
    function init() {
        applyChainUi();
        var p = new URLSearchParams(window.location.search);
        var len = parseInt(p.get('len'), 10); if (len === 22 || len === 30) L = len;
        setActiveFormatCard();
        if (IS_BTC) { var ty = p.get('type'); if (ty && TYPE_META[ty]) ADDR_TYPE = ty; setActiveTypeCard(); }
        var startIdx = 0n, iStr = p.get('i');
        if (iStr) { try { var ord = BigInt(iStr); if (ord < 1n) ord = 1n; startIdx = pageStart(ord - 1n); } catch (e) {} }

        var jb = document.getElementById('btn-jump'); if (jb) jb.addEventListener('click', window.MK_jump);
        var pin = document.getElementById('pageInput');
        if (pin) pin.addEventListener('keydown', function (e) { if (e.key === 'Enter') { e.preventDefault(); window.MK_jump(); } });

        var cont = document.getElementById('keysContainer');
        if (cont) cont.addEventListener('click', function (e) {
            var b = e.target && e.target.closest ? e.target.closest('.copy-btn') : null;
            if (!b) return; e.preventDefault();
            MK_copy(b.getAttribute('data-copy'));
        });

        window.addEventListener('popstate', function () {
            var pp = new URLSearchParams(window.location.search);
            var l = parseInt(pp.get('len'), 10); if (l === 22 || l === 30) { L = l; setActiveFormatCard(); }
            if (IS_BTC) { var t = pp.get('type'); if (t && TYPE_META[t]) { ADDR_TYPE = t; setActiveTypeCard(); } }
            var s = 0n, is = pp.get('i');
            if (is) { try { var o = BigInt(is); if (o < 1n) o = 1n; s = pageStart(o - 1n); } catch (e) {} }
            renderPage(s, true);
        });

        window.CGT_ENGINE = { goToKey: function (ord) { goTo(pageStart((ord > 0n ? ord : 1n) - 1n)); }, setFormat: window.MK_setFormat };
        window.MK = { goTo: goTo, setFormat: window.MK_setFormat, setType: window.MK_setType, jump: window.MK_jump, indexToMiniKey: indexToMiniKey };

        renderPage(startIdx, true);
        selfTest();
    }

    if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', init);
    else init();
})();
