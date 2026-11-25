/*
 * Profanity Vanity Weak Keys — modeled 32-bit-seed scanner (the Wintermute
 * hack), with multi-chain address support.
 *
 * Profanity (johguse/profanity, 2018) generated Ethereum vanity addresses
 * from a single 32-bit seed. Every private key it produced is a simple
 * function of that seed and an attempt counter — the classic recovery
 * (keyhunt's profanity mode, used in the $115M Wintermute hack) brute-forces
 * d = seed + offset over the 32-bit seed space.
 *
 * This tool MODELS that collapse exactly as the real attack worked:
 *
 *     d = (seed + offset) mod n
 *
 *   • Verify — derive the key + addresses for one (seed, offset) pair.
 *   • Scan   — brute a seed × offset rectangle for a target address (bounded
 *              Web Worker, Jacobian scalar-mul; chunked main-thread fallback).
 *
 * Every hit is verified by regenerating the address, so there are no false
 * positives. The recovered key is a plain secp256k1 key, so once found it
 * derives addresses for every secp256k1-based chain — Bitcoin-family P2PKH,
 * every EVM chain + TRON via keccak-256, and XRP via hash160 + the XRP base58
 * alphabet. Solana / TON / Sui use Ed25519, not secp256k1, so they cannot be
 * derived — the UI says so instead of guessing.
 *
 * HONEST SCOPE: the full Profanity keyspace is 2^32 seeds — too large for a
 * browser in one pass; this scans bounded slices and shows why a 32-bit seed
 * is catastrophic. It recovers any key generated under this model.
 *
 * Depends only on CryptoJS (loaded before this file). Exposes window.processTxid
 * (scan), window.verifyPid, window.exportOne.
 */
(function () {
    "use strict";

    // ---- Constants -------------------------------------------------------
    const BTC_ALPHABET = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";
    const XRP_ALPHABET = "rpshnaf39wBUDNEGHJKLM4PQRST7VWXYZ2bcdeCg65jkm8oFqi1tuvAxyz";
    const N = BigInt('0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141');
    const P_CURVE = (2n ** 256n) - (2n ** 32n) - 977n;
    const Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798n;
    const Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8n;
    const MAX_CHECKS = 2000000;      // guard: cap seed × offset work at 2M keys

    // ---- Chain registry --------------------------------------------------
    var CHAINS = {
        bitcoin:       { name: 'Bitcoin',      kind: 'p2pkh',   version: '00' },
        ethereum:      { name: 'Ethereum',     kind: 'evm' },
        bnb:           { name: 'BNB Chain',    kind: 'evm' },
        arbitrum:      { name: 'Arbitrum',     kind: 'evm' },
        optimism:      { name: 'Optimism',     kind: 'evm' },
        base:          { name: 'Base',         kind: 'evm' },
        polygon:       { name: 'Polygon',      kind: 'evm' },
        avalanche:     { name: 'Avalanche',    kind: 'evm' },
        zksync:        { name: 'zkSync Era',   kind: 'evm' },
        solana:        { name: 'Solana',       kind: 'ed25519' },
        tron:          { name: 'Tron',         kind: 'tron' },
        toncoin:       { name: 'TON',          kind: 'ed25519' },
        sui:           { name: 'Sui',          kind: 'ed25519' },
        xrp:           { name: 'XRP',          kind: 'xrp' },
        litecoin:      { name: 'Litecoin',     kind: 'p2pkh',   version: '30' },
        'bitcoin-cash':{ name: 'Bitcoin Cash', kind: 'p2pkh',   version: '00' },
        dogecoin:      { name: 'Dogecoin',     kind: 'p2pkh',   version: '1e' },
        zcash:         { name: 'Zcash',        kind: 'zcash',   version: '1cb8' }
    };
    function chainInfo(c) { return CHAINS[c] || CHAINS.bitcoin; }

    // ---- Low-level converters -------------------------------------------
    function hexToBytes(hex) {
        if (!hex || typeof hex !== 'string') return new Uint8Array();
        if (hex.length % 2 !== 0) hex = '0' + hex;
        const m = hex.match(/.{1,2}/g);
        return m ? new Uint8Array(m.map(b => parseInt(b, 16))) : new Uint8Array();
    }
    function bytesToHex(bytes) {
        return Array.from(bytes).map(b => b.toString(16).padStart(2, '0')).join('');
    }
    function hx64(b) { let s = b.toString(16); while (s.length < 64) s = "0" + s; return s; }

    // ---- Hashing (CryptoJS) ---------------------------------------------
    function sha256hex(hex) { return CryptoJS.SHA256(CryptoJS.enc.Hex.parse(hex)).toString(); }
    function ripe160hex(hex) { return CryptoJS.RIPEMD160(CryptoJS.enc.Hex.parse(hex)).toString(); }
    function dblsha256(hex) { return sha256hex(sha256hex(hex)); }
    function hash160Hex(pubHex) { return ripe160hex(sha256hex(pubHex)); }

    // ---- keccak-256 (Ethereum / TRON) -----------------------------------
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
        return bytesToHex(out);
    }

    // ---- Base58 / addresses ---------------------------------------------
    function b58encode(hex, alphabet) {
        var A = alphabet || BTC_ALPHABET;
        let num = BigInt("0x" + hex), str = "";
        while (num > 0n) { str = A[Number(num % 58n)] + str; num /= 58n; }
        for (let i = 0; i < hex.length; i += 2) { if (hex.substring(i, i + 2) === "00") str = A[0] + str; else break; }
        return str;
    }
    function b58decodeToHex(s, alphabet) {
        var A = alphabet || BTC_ALPHABET;
        let num = 0n;
        for (const ch of s) {
            const i = A.indexOf(ch);
            if (i < 0) throw new Error("Invalid address character '" + ch + "'");
            num = num * 58n + BigInt(i);
        }
        let hex = num.toString(16);
        if (hex.length % 2) hex = "0" + hex;
        let zeros = 0;
        for (const ch of s) { if (ch === A[0]) zeros++; else break; }
        return "00".repeat(zeros) + hex;
    }
    function b58checkDecode(s, alphabet) {
        const hex = b58decodeToHex(s.trim(), alphabet);
        if (hex.length < 10) throw new Error("Address too short");
        const payload = hex.slice(0, -8), checksum = hex.slice(-8);
        return { payload: payload, checksumOk: dblsha256(payload).slice(0, 8) === checksum };
    }
    function base58checkAddr(payloadHex) { return b58encode(payloadHex + dblsha256(payloadHex).slice(0, 8)); }
    function base58checkAddrXrp(payloadHex) { return b58encode(payloadHex + dblsha256(payloadHex).slice(0, 8), XRP_ALPHABET); }
    function addrFromPub(pubHex, version) { return base58checkAddr(version + hash160Hex(pubHex)); }
    function privToWif(privHex, compressed) {
        const payload = "80" + privHex + (compressed ? "01" : "");
        return b58encode(payload + dblsha256(payload).slice(0, 8));
    }

    // ---- secp256k1 (Jacobian scalar-mul) --------------------------------
    function mod(a, m) { const r = a % m; return r < 0n ? r + m : r; }
    function egcd(a, b) { if (b === 0n) return [a, 1n, 0n]; const r = egcd(b, a % b); return [r[0], r[2], r[1] - (a / b) * r[2]]; }
    function modInv(a, m) { a = mod(a, m); const r = egcd(a, m); return mod(r[1], m); }
    function jDouble(Pp) {
        const Y = Pp.Y; if (Y === 0n) return { X: 0n, Y: 0n, Z: 0n };
        const X = Pp.X, Z = Pp.Z;
        const A = mod(X * X, P_CURVE), B = mod(Y * Y, P_CURVE), C = mod(B * B, P_CURVE);
        const D = mod(2n * (mod((X + B) * (X + B), P_CURVE) - A - C), P_CURVE);
        const E = mod(3n * A, P_CURVE), F = mod(E * E, P_CURVE);
        const X3 = mod(F - 2n * D, P_CURVE);
        return { X: X3, Y: mod(E * (D - X3) - 8n * C, P_CURVE), Z: mod(2n * Y * Z, P_CURVE) };
    }
    function jAdd(Pp, Qp) {
        if (Pp.Z === 0n) return Qp; if (Qp.Z === 0n) return Pp;
        const Z1Z1 = mod(Pp.Z * Pp.Z, P_CURVE), Z2Z2 = mod(Qp.Z * Qp.Z, P_CURVE);
        const U1 = mod(Pp.X * Z2Z2, P_CURVE), U2 = mod(Qp.X * Z1Z1, P_CURVE);
        const S1 = mod(mod(Pp.Y * Qp.Z, P_CURVE) * Z2Z2, P_CURVE), S2 = mod(mod(Qp.Y * Pp.Z, P_CURVE) * Z1Z1, P_CURVE);
        if (U1 === U2) { if (S1 !== S2) return { X: 0n, Y: 0n, Z: 0n }; return jDouble(Pp); }
        const H = mod(U2 - U1, P_CURVE), I = mod((2n * H) * (2n * H), P_CURVE), J = mod(H * I, P_CURVE);
        const r = mod(2n * (S2 - S1), P_CURVE), V = mod(U1 * I, P_CURVE);
        const X3 = mod(r * r - J - 2n * V, P_CURVE);
        return {
            X: X3,
            Y: mod(r * (V - X3) - 2n * S1 * J, P_CURVE),
            Z: mod((mod((Pp.Z + Qp.Z) * (Pp.Z + Qp.Z), P_CURVE) - Z1Z1 - Z2Z2) * H, P_CURVE)
        };
    }
    function sMul(k) {
        k = mod(k, N); let R = { X: 0n, Y: 0n, Z: 0n }, A = { X: Gx, Y: Gy, Z: 1n };
        while (k > 0n) { if (k & 1n) R = jAdd(R, A); A = jDouble(A); k >>= 1n; }
        if (R.Z === 0n) return null;
        const zi = modInv(R.Z, P_CURVE), zi2 = mod(zi * zi, P_CURVE), zi3 = mod(zi2 * zi, P_CURVE);
        return { x: mod(R.X * zi2, P_CURVE), y: mod(R.Y * zi3, P_CURVE) };
    }
    function pubsFromPriv(d) {
        const Q = sMul(d);
        const x = hx64(Q.x), y = hx64(Q.y);
        return { x: x, y: y, cpub: (Q.y & 1n ? "03" : "02") + x, upub: "04" + x + y };
    }

    // ---- Modeled Profanity derivation -----------------------------------
    // d = (seed + offset) mod n — the exact structure keyhunt's profanity
    // recovery brute-forces (seed = 32-bit Profanity seed, offset = the
    // attempt counter within the generated batch).
    function deriveProfanityPriv(seed, offset) {
        return (BigInt(seed >>> 0) + BigInt(offset >>> 0)) % N;
    }

    // ---- Multi-chain address derivation ----------------------------------
    function chainAddresses(pk, c) {
        var info = chainInfo(c);
        if (info.kind === 'p2pkh' || info.kind === 'zcash') {
            return [addrFromPub(pk.cpub, info.version), addrFromPub(pk.upub, info.version)];
        }
        if (info.kind === 'evm' || info.kind === 'tron') {
            var k = keccak256Hex(hexToBytes(pk.upub.slice(2))).slice(-40);
            if (info.kind === 'tron') return [base58checkAddr("41" + k)];
            return ["0x" + k.toLowerCase()];
        }
        if (info.kind === 'xrp') return [base58checkAddrXrp("00" + hash160Hex(pk.cpub))];
        return [];
    }
    function chainCompareValue(pk, c) {
        var info = chainInfo(c);
        if (info.kind === 'evm') return "0x" + keccak256Hex(hexToBytes(pk.upub.slice(2))).slice(-40);
        if (info.kind === 'tron') return keccak256Hex(hexToBytes(pk.upub.slice(2))).slice(-40);
        if (info.kind === 'xrp') return hash160Hex(pk.cpub);
        return hash160Hex(pk.cpub);
    }
    function parseTarget(c, raw) {
        var info = chainInfo(c);
        if (info.kind === 'ed25519') {
            throw new Error(info.name + " uses the Ed25519 curve — a secp256k1 key cannot derive a " + info.name + " address. Switch to a secp256k1 chain (Bitcoin, EVM, TRON, XRP, Litecoin…).");
        }
        if (info.kind === 'evm') {
            var s = String(raw || "").trim();
            var evm = /^(0x)?[0-9a-fA-F]{40}$/.exec(s);
            if (!evm) throw new Error("Enter a valid " + info.name + " address (0x + 40 hex characters).");
            var hex = evm[1] ? s.slice(2) : s;
            return { ok: true, target: "0x" + hex.toLowerCase(), kind: 'evm', addr: "0x" + hex.toLowerCase() };
        }
        var alphabet = info.kind === 'xrp' ? XRP_ALPHABET : BTC_ALPHABET;
        var dec;
        try { dec = b58checkDecode(raw, alphabet); }
        catch (e) { throw new Error(e.message); }
        if (!dec.checksumOk) throw new Error("Bad checksum — not a valid address");
        var version = info.kind === 'zcash' ? dec.payload.slice(0, 4) : dec.payload.slice(0, 2);
        var expectedV = info.kind === 'zcash' ? "1cb8" : info.kind === 'tron' ? "41" : info.kind === 'xrp' ? "00" : info.version;
        if (version.toLowerCase() !== expectedV.toLowerCase()) {
            throw new Error("That address is not a " + info.name + " address (version byte 0x" + version + ").");
        }
        var hash = info.kind === 'zcash' ? dec.payload.slice(4) : dec.payload.slice(2);
        return { ok: true, target: hash.toLowerCase(), kind: info.kind, addr: String(raw || "").trim() };
    }

    // ---- Bounded brute (Web Worker) --------------------------------------
    // Message in : {target, kind, lo, hi, offLo, offHi}.
    function profWorkerBody() {
        "use strict";
        try { importScripts("https://cdnjs.cloudflare.com/ajax/libs/crypto-js/4.1.1/crypto-js.min.js"); }
        catch (e) { postMessage({ type: "noimport" }); return; }

        var N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141n;
        var P = (2n ** 256n) - (2n ** 32n) - 977n;
        var Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798n;
        var Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8n;

        function mod(a, m) { var r = a % m; return r < 0n ? r + m : r; }
        function egcd(a, b) { if (b === 0n) return [a, 1n, 0n]; var r = egcd(b, a % b); return [r[0], r[2], r[1] - (a / b) * r[2]]; }
        function modInv(a, m) { a = mod(a, m); var r = egcd(a, m); return mod(r[1], m); }
        function jD(Pp) {
            var Y = Pp.Y; if (Y === 0n) return { X: 0n, Y: 0n, Z: 0n };
            var X = Pp.X, Z = Pp.Z, A = mod(X * X, P), B = mod(Y * Y, P), C = mod(B * B, P);
            var D = mod(2n * (mod((X + B) * (X + B), P) - A - C), P), E = mod(3n * A, P), F = mod(E * E, P);
            var X3 = mod(F - 2n * D, P);
            return { X: X3, Y: mod(E * (D - X3) - 8n * C, P), Z: mod(2n * Y * Z, P) };
        }
        function jA(Pp, Qp) {
            if (Pp.Z === 0n) return Qp; if (Qp.Z === 0n) return Pp;
            var Z1 = mod(Pp.Z * Pp.Z, P), Z2 = mod(Qp.Z * Qp.Z, P);
            var U1 = mod(Pp.X * Z2, P), U2 = mod(Qp.X * Z1, P);
            var S1 = mod(mod(Pp.Y * Qp.Z, P) * Z2, P), S2 = mod(mod(Qp.Y * Pp.Z, P) * Z1, P);
            if (U1 === U2) { if (S1 !== S2) return { X: 0n, Y: 0n, Z: 0n }; return jD(Pp); }
            var H = mod(U2 - U1, P), I = mod((2n * H) * (2n * H), P), J = mod(H * I, P);
            var r = mod(2n * (S2 - S1), P), V = mod(U1 * I, P), X3 = mod(r * r - J - 2n * V, P);
            return { X: X3, Y: mod(r * (V - X3) - 2n * S1 * J, P), Z: mod((mod((Pp.Z + Qp.Z) * (Pp.Z + Qp.Z), P) - Z1 - Z2) * H, P) };
        }
        function sMul(k) {
            k = mod(k, N); var R = { X: 0n, Y: 0n, Z: 0n }, A = { X: Gx, Y: Gy, Z: 1n };
            while (k > 0n) { if (k & 1n) R = jA(R, A); A = jD(A); k >>= 1n; }
            if (R.Z === 0n) return null;
            var zi = modInv(R.Z, P), zi2 = mod(zi * zi, P), zi3 = mod(zi2 * zi, P);
            return { x: mod(R.X * zi2, P), y: mod(R.Y * zi3, P) };
        }
        function hx(b) { var s = b.toString(16); while (s.length < 64) s = "0" + s; return s; }
        function h160(pub) { return CryptoJS.RIPEMD160(CryptoJS.SHA256(CryptoJS.enc.Hex.parse(pub))).toString(); }
        function derive(seed, offset) {
            var d = (BigInt(seed >>> 0) + BigInt(offset >>> 0)) % N;
            return d;
        }
        // --- keccak-256 (in-worker) ---
        var RC = [0x0000000000000001n, 0x0000000000008082n, 0x800000000000808an, 0x8000000080008000n, 0x000000000000808bn, 0x0000000080000001n, 0x8000000080008081n, 0x8000000000008009n, 0x000000000000008an, 0x0000000000000088n, 0x0000000080008009n, 0x000000008000000an, 0x000000008000808bn, 0x800000000000008bn, 0x8000000000008089n, 0x8000000000008003n, 0x8000000000008002n, 0x8000000000000080n, 0x000000000000800an, 0x800000008000000an, 0x8000000080008081n, 0x8000000000008080n, 0x0000000080000001n, 0x8000000080008008n];
        var RHO = [1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 2, 14, 27, 41, 56, 8, 25, 43, 62, 18, 39, 61, 20, 44];
        var PILN = [10, 7, 11, 17, 18, 3, 5, 16, 8, 21, 24, 4, 15, 23, 19, 13, 12, 2, 20, 14, 22, 9, 6, 1];
        var M64 = (1n << 64n) - 1n;
        function rol(x, s) { s = s % 64n; return s === 0n ? x : ((x << s) | (x >> (64n - s))) & M64; }
        function kF(a) {
            var B = new Array(25).fill(0n), C = [0n, 0n, 0n, 0n, 0n], x, y, i, t, j, v, D;
            for (var round = 0; round < 24; round++) {
                for (x = 0; x < 5; x++) C[x] = a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20];
                for (x = 0; x < 5; x++) {
                    D = C[(x + 4) % 5] ^ rol(C[(x + 1) % 5], 1n);
                    for (y = 0; y < 5; y++) a[x + 5 * y] ^= D;
                }
                t = a[1];
                for (x = 0; x < 24; x++) {
                    j = PILN[x]; v = a[j];
                    a[j] = rol(t, BigInt(RHO[x]));
                    t = v;
                }
                for (y = 0; y < 5; y++) {
                    for (x = 0; x < 5; x++) B[x + 5 * y] = a[x + 5 * y] ^ ((~a[(x + 1) % 5 + 5 * y]) & a[(x + 2) % 5 + 5 * y]);
                }
                for (i = 0; i < 25; i++) a[i] = B[i];
                a[0] ^= RC[round];
            }
        }
        function keccak(bytes) {
            var rate = 136, st = new BigUint64Array(25), buf = new Uint8Array(bytes);
            var full = Math.floor(buf.length / rate), b, i, off, k, lane;
            for (b = 0; b < full; b++) {
                for (i = 0; i < rate / 8; i++) {
                    off = b * rate + i * 8; lane = 0n;
                    for (k = 7; k >= 0; k--) lane = (lane << 8n) | BigInt(buf[off + k]);
                    st[i] ^= lane;
                }
                kF(st);
            }
            var rem = buf.length - full * rate, last = new Uint8Array(rate);
            last.set(buf.subarray(full * rate));
            last[rem] ^= 0x01; last[rate - 1] ^= 0x80;
            for (i = 0; i < rate / 8; i++) {
                off = i * 8; lane = 0n;
                for (k = 7; k >= 0; k--) lane = (lane << 8n) | BigInt(last[off + k]);
                st[i] ^= lane;
            }
            kF(st);
            var out = new Uint8Array(32), o = 0, hex = "";
            for (i = 0; i < 4; i++) {
                lane = st[i];
                for (k = 0; k < 8; k++) { out[o++] = Number(lane & 0xffn); lane >>= 8n; }
            }
            for (i = 0; i < out.length; i++) hex += out[i].toString(16).padStart(2, "0");
            return hex;
        }
        function bytesOfHex(h) {
            var out = new Uint8Array(h.length / 2);
            for (var i = 0; i < out.length; i++) out[i] = parseInt(h.substring(i * 2, i * 2 + 2), 16);
            return out;
        }
        function compareValue(Q, kind) {
            var xh = hx(Q.x), yh = hx(Q.y);
            var cpub = (Q.y & 1n ? "03" : "02") + xh;
            var upub = "04" + xh + yh;
            if (kind === 'evm') return "0x" + keccak(bytesOfHex(upub.slice(2))).slice(-40);
            if (kind === 'tron') return keccak(bytesOfHex(upub.slice(2))).slice(-40);
            if (kind === 'xrp') return h160(cpub);
            return h160(cpub);
        }

        onmessage = function (e) {
            var lo = e.data.lo, hi = e.data.hi, offLo = e.data.offLo, offHi = e.data.offHi;
            var target = (e.data.target || "").toLowerCase();
            var kind = e.data.kind || 'p2pkh';
            var wantUpub = (kind === 'p2pkh' || kind === 'zcash');
            var checked = 0, total = (hi - lo + 1) * (offHi - offLo + 1);
            for (var seed = lo; seed <= hi; seed++) {
                for (var off = offLo; off <= offHi; off++) {
                    var d = derive(seed, off), Q = sMul(d);
                    if (!Q) { checked++; continue; }
                    var xh = hx(Q.x);
                    if (wantUpub) {
                        var cpub = (Q.y & 1n ? "03" : "02") + xh;
                        if (h160(cpub) === target || h160("04" + xh + hx(Q.y)) === target) {
                            postMessage({ type: "found", seed: seed, offset: off, priv: hx(d), format: h160(cpub) === target ? "compressed" : "uncompressed" });
                            return;
                        }
                    } else {
                        if (compareValue(Q, kind) === target) {
                            postMessage({ type: "found", seed: seed, offset: off, priv: hx(d), format: "chain" });
                            return;
                        }
                    }
                    checked++;
                }
                if ((seed & 511) === 0) postMessage({ type: "progress", checked: checked, total: total, seed: seed });
            }
            postMessage({ type: "done", checked: checked });
        };
    }

    var WORKER_SRC = '(' + profWorkerBody.toString() + ')()';
    var _workerURL = null;
    function buildWorker() {
        try {
            if (typeof Worker === 'undefined' || typeof URL === 'undefined' || !URL.createObjectURL) return null;
            if (!_workerURL) _workerURL = URL.createObjectURL(new Blob([WORKER_SRC], { type: 'application/javascript' }));
            return new Worker(_workerURL);
        } catch (e) { return null; }
    }

    function compareKeyForChain(d, chain, target) {
        var pk = pubsFromPriv(d);
        var info = chainInfo(chain);
        if (info.kind === 'p2pkh' || info.kind === 'zcash') {
            if (hash160Hex(pk.cpub) === target) return { format: "compressed" };
            if (hash160Hex(pk.upub) === target) return { format: "uncompressed" };
            return null;
        }
        return chainCompareValue(pk, chain) === target ? { format: "chain" } : null;
    }

    function mainThreadScan(chain, target, lo, hi, offLo, offHi, onProgress) {
        return new Promise(function (resolve) {
            let seed = lo, checked = 0; const total = (hi - lo + 1) * (offHi - offLo + 1);
            function chunk() {
                const end = Math.min(hi, seed + 99);
                for (; seed <= end; seed++) {
                    for (let off = offLo; off <= offHi; off++) {
                        const d = deriveProfanityPriv(seed, off), m = compareKeyForChain(d, chain, target);
                        if (m) { resolve({ found: true, seed: seed, offset: off, priv: hx64(d), format: m.format }); return; }
                        checked++;
                    }
                }
                if (onProgress) onProgress({ checked: checked, total: total, seed: end });
                if (seed <= hi) setTimeout(chunk, 0); else resolve({ found: false, checked: checked });
            }
            chunk();
        });
    }

    function runScan(chain, target, kind, lo, hi, offLo, offHi, onProgress) {
        return new Promise(function (resolve) {
            const w = buildWorker();
            if (!w) { mainThreadScan(chain, target, lo, hi, offLo, offHi, onProgress).then(resolve); return; }
            let fellBack = false;
            const fallback = function () { if (fellBack) return; fellBack = true; try { w.terminate(); } catch (e) { } mainThreadScan(chain, target, lo, hi, offLo, offHi, onProgress).then(resolve); };
            w.onmessage = function (ev) {
                const m = ev.data;
                if (m.type === 'noimport') { fallback(); }
                else if (m.type === 'progress') { if (onProgress) onProgress(m); }
                else if (m.type === 'found') { try { w.terminate(); } catch (e) { } resolve({ found: true, seed: m.seed, offset: m.offset, priv: m.priv, format: m.format }); }
                else if (m.type === 'done') { try { w.terminate(); } catch (e) { } resolve({ found: false, checked: m.checked }); }
            };
            w.onerror = function () { fallback(); };
            w.postMessage({ target: target, kind: kind, lo: lo, hi: hi, offLo: offLo, offHi: offHi });
        });
    }

    // ---- Output header + export ------------------------------------------
    function getOutputHeader(elementId) {
        let header = `<div class="result-header">CRYPTOGRAPHYTUBE<span class="tool-tag">Profanity Seed Scan</span></div>`;
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
        if (!el || el.innerText.trim() === "" || el.innerText.includes("Instructions:") || el.innerText.length < 5) {
            alert("No results to export for this section yet.");
            return;
        }
        const section = el.closest('.tool-section');
        const title = section ? (section.querySelector('h3') ? section.querySelector('h3').innerText : "CryptographyTube Result") : "CryptographyTube Result";
        let headerText = `CRYPTOGRAPHYTUBE REPORT\n`;
        headerText += `TOOL: ${title.toUpperCase()}\n`;
        headerText += `GENERATED: ${new Date().toLocaleString()}\n`;
        headerText += `--------------------------------------------------\n\n`;
        const fullContent = headerText + (el.innerText || el.textContent);
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
    function rszLine(label, val) {
        return '<div class="rsz-line"><span class="rsz-tag">' + label + '</span>' +
            '<code class="rsz-val">' + escapeHtml(val || '—') + '</code>' + copyBtn(val) + '</div>';
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
        } catch (e) { /* ignore */ }
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
        const n = size || 13;
        return '<img src="../assets/svgs/solid/spinner.svg" class="txr-spin" width="' + n + '" height="' + n + '" alt="loading">';
    }

    // ---- Renderers -------------------------------------------------------
    function keyBlock(seed, offset, d, chain, matchedFormat) {
        const pk = pubsFromPriv(d);
        const priv = hx64(d);
        const info = chainInfo(chain);
        let h = '';
        h += '<div class="rsz-vuln-box">';
        h += '<div class="rsz-vuln-title"><img src="../assets/svgs/solid/triangle-exclamation.svg" width="15" height="15" alt=""> ' +
            'WEAK KEY — seed ' + seed + ' + offset ' + offset + ' · ' + escapeHtml(info.name) +
            (matchedFormat ? ' · matched ' + matchedFormat + ' address' : '') + '</div>';
        h += '<div class="rsz-vuln-key"><span class="key-label">Private key</span>' +
            '<span class="private-key">' + escapeHtml(priv) + '</span>' + copyBtn(priv) + '</div>';
        h += rszLine('WIF (compressed)', privToWif(priv, true));
        h += rszLine('WIF (uncompressed)', privToWif(priv, false));
        if (info.kind === 'p2pkh' || info.kind === 'zcash') {
            h += addrLine('Address (compressed)', addrFromPub(pk.cpub, info.version));
            h += addrLine('Address (uncompressed)', addrFromPub(pk.upub, info.version));
        } else {
            const addrs = chainAddresses(pk, chain);
            if (addrs.length) h += addrLine(info.name + ' address', addrs[0]);
        }
        h += rszLine('Public key (compressed)', pk.cpub);
        if (matchedFormat) {
            h += '<div class="rsz-leak-bits">Recovered by scanning the seed × offset rectangle — the address regenerates from this key (' +
                escapeHtml(matchedFormat) + (matchedFormat === 'chain' ? ' address' : ' P2PKH') +
                '), so the match is verified, not guessed.</div>';
        }
        h += '</div>';
        return h;
    }

    function renderScanResult(res, lo, hi, offLo, offHi, targetAddr, chain) {
        const info = chainInfo(chain);
        let html = '';
        html += '<div class="rsz-summary">';
        html += '<span class="rsz-chip">' + escapeHtml(info.name) + '</span>';
        html += '<span class="rsz-chip">seed ' + lo + '–' + hi + ' × offset ' + offLo + '–' + offHi + '</span>';
        html += '<span class="rsz-chip">' + (res.checked != null ? res.checked.toLocaleString() : ((hi - lo + 1) * (offHi - offLo + 1)).toLocaleString()) + ' keys tested</span>';
        if (res.found) html += '<span class="rsz-chip rsz-chip-danger">Weak key recovered</span>';
        else html += '<span class="rsz-chip rsz-chip-ok">No weak key in range</span>';
        html += '</div>';
        html += '<div class="rsz-line"><span class="rsz-tag">TARGET</span>' +
            '<code class="rsz-val rsz-addr-val">' + escapeHtml(targetAddr) + '</code>' + copyBtn(targetAddr) + '</div>';
        if (res.found) {
            html += keyBlock(res.seed, res.offset, BigInt('0x' + res.priv), chain, res.format);
        } else {
            html += '<div class="rsz-leak-note rsz-leak-ok">Scanned ' + ((hi - lo + 1) * (offHi - offLo + 1)).toLocaleString() +
                ' keys (seed × offset) for a ' + escapeHtml(info.name) + ' address — no key in this rectangle produced it. ' +
                'The full Profanity space is 2^32 seeds; widen the ranges in slices or try another slice.</div>';
        }
        return html;
    }

    function renderVerify(seed, offset, chain) {
        const info = chainInfo(chain);
        const d = deriveProfanityPriv(seed, offset);
        let html = '';
        html += '<div class="rsz-summary">';
        html += '<span class="rsz-chip">seed ' + seed + ' + offset ' + offset + '</span>';
        html += '<span class="rsz-chip rsz-chip-danger">1 key derived</span>';
        html += '</div>';
        html += '<div class="rsz-leak-note">Profanity derived every key from its 32-bit seed as d = seed + offset. ' +
            'Paste the ' + escapeHtml(info.name) + ' address below into <strong>Scan</strong> to watch the rectangle brute recover it.</div>';
        html += keyBlock(seed, offset, d, chain, null);
        return html;
    }

    // ---- Entry points ----------------------------------------------------
    function activeChain() { return window.TXR_CHAIN || 'ethereum'; }
    function readRange() {
        const loEl = document.getElementById('range_lo');
        const hiEl = document.getElementById('range_hi');
        const offEl = document.getElementById('off_hi');
        let lo = loEl ? parseInt(loEl.value, 10) : 0;
        let hi = hiEl ? parseInt(hiEl.value, 10) : 4095;
        let offHi = offEl ? parseInt(offEl.value, 10) : 31;
        if (!Number.isFinite(lo) || lo < 0) lo = 0;
        if (!Number.isFinite(hi) || hi < 0) hi = 4095;
        if (!Number.isFinite(offHi) || offHi < 0) offHi = 31;
        if (hi < lo) { const t = lo; lo = hi; hi = t; }
        const span = (hi - lo + 1) * (offHi + 1);
        if (span > MAX_CHECKS) {
            hi = lo + Math.max(0, Math.floor(MAX_CHECKS / (offHi + 1)) - 1);
        }
        return { lo: lo, hi: hi, offLo: 0, offHi: offHi };
    }

    async function processTxid() {
        const input = (document.getElementById("target_input") || {}).value;
        const out = document.getElementById("out_txid");
        if (!out) return;
        const header = getOutputHeader(out.id);
        const chain = activeChain();
        const info = chainInfo(chain);
        const addr = (input || "").trim();
        if (!addr) { out.innerHTML = header + '<div class="rsz-error"><img src="../assets/svgs/solid/triangle-exclamation.svg" width="14" height="14" alt=""> Enter a ' + escapeHtml(info.name) + ' address to recover.</div>'; return; }

        let target;
        try { target = parseTarget(chain, addr); }
        catch (e) { out.innerHTML = header + '<div class="rsz-error"><img src="../assets/svgs/solid/triangle-exclamation.svg" width="14" height="14" alt=""> ' + escapeHtml(e.message) + '</div>'; return; }

        const { lo, hi, offLo, offHi } = readRange();
        const t0 = Date.now();
        const total = (hi - lo + 1) * (offHi - offLo + 1);
        const setStatus = function (msg) { out.innerHTML = header + '<div class="rsz-status">' + spinner(14) + ' ' + escapeHtml(msg) + '</div>'; };
        setStatus('Scanning seeds ' + lo + '–' + hi + ' × offsets 0–' + offHi + ' (' + total.toLocaleString() + ' keys) for a ' + info.name + ' address (' + addr + ')…');

        const res = await runScan(chain, target.target, target.kind, lo, hi, offLo, offHi, function (p) {
            const pct = p.total ? Math.floor((p.checked / p.total) * 100) : 0;
            setStatus('Scanning… seed ' + (p.seed != null ? p.seed : '?') + ' / ' + hi + '  (' + pct + '%, ' + p.checked.toLocaleString() + ' keys)');
        });
        res._ms = Date.now() - t0;
        out.innerHTML = header + renderScanResult(res, lo, hi, offLo, offHi, target.addr, chain) +
            '<div class="rsz-leak-note" style="margin-top:.6rem">Scan finished in ' + (res._ms / 1000).toFixed(1) + ' s.</div>';
    }

    function verifyPid() {
        const out = document.getElementById("out_txid");
        if (!out) return;
        const header = getOutputHeader(out.id);
        const chain = activeChain();
        const rawSeed = (document.getElementById('seed_input') || {}).value;
        const rawOff = (document.getElementById('offset_input') || {}).value;
        const seed = parseInt((rawSeed || "").trim(), 10);
        const offset = parseInt((rawOff || "").trim(), 10);
        if (!Number.isFinite(seed) || seed < 0 || seed > 0xFFFFFFFF) {
            out.innerHTML = header + '<div class="rsz-error"><img src="../assets/svgs/solid/triangle-exclamation.svg" width="14" height="14" alt=""> Enter a 32-bit seed (0 to 4294967295, e.g. 1337).</div>';
            return;
        }
        const o = Number.isFinite(offset) && offset >= 0 ? offset : 0;
        out.innerHTML = header + renderVerify(seed >>> 0, o, chain);
    }

    // ---- Expose ----------------------------------------------------------
    window.processTxid = processTxid;   // Scan
    window.verifyPid = verifyPid;       // Verify a seed + offset
    window.exportOne = exportOne;
})();
