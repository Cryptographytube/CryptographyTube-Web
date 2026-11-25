/*
 * Randstorm Checker — modeled BitcoinJS SecureRandom (2011–2015) key scanner,
 * with multi-chain address support.
 *
 * In 2011–2015 BitcoinJS-based wallet sites (bitaddress.org-era generators,
 * early blockchain.info) created keys with a SecureRandom pool seeded by only
 * a handful of weak sources: a timestamp plus a few Math.random() draws
 * (plus predictable browser properties). Effectively the whole 256-byte pool —
 * and therefore every private key it produced — was determined by roughly
 * 32 bits of real entropy ("Randstorm").
 *
 * This tool MODELS that collapse. A single 32-bit seed (the collapsed entropy)
 * is expanded into the 256-byte pool the way the vulnerable class of RNGs
 * worked (timestamp + LCG Math.random draws stretched to 256 bytes), then run
 * through the RC4-style key-scheduling algorithm BitcoinJS used, and the
 * stream cipher's first 32 bytes become the private key:
 *
 *     seed -> 4×LCG draws -> 16-byte pool head -> expansion to 256 bytes
 *            -> RC4 KSA+PRGA -> 32 bytes -> d (mod n)
 *
 * HONEST SCOPE: this models the *collapse to a 32-bit seed*; it is NOT a
 * byte-exact reproduction of a specific BitcoinJS build, so it will not
 * recover keys from real historical wallets without the exact wallet-creation
 * parameters. It recovers any key generated under this model and shows why a
 * weak browser RNG is catastrophic. All secp256k1 and address math is real;
 * every hit is verified by regenerating the address.
 *
 * Chain support: a recovered secp256k1 key derives addresses for every
 * secp256k1-based chain — Bitcoin-family P2PKH (BTC/LTC/DOGE/ZEC/BCH legacy),
 * every EVM chain (ETH/BNB/ARB/OP/BASE/MATIC/AVAX/ZKSYNC) and TRON via
 * keccak-256, and XRP via hash160 + the XRP base58 alphabet. Solana / TON /
 * Sui use Ed25519, not secp256k1, so they cannot be derived from this key —
 * the UI says so instead of guessing.
 *
 * Two modes (no network):
 *   • Verify a seed — derive the key + addresses for the selected chain.
 *   • Scan a target — brute a seed range for the target address on the
 *                     selected chain (bounded Web Worker, Jacobian scalar-mul,
 *                     chunked main-thread fallback).
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
    const MAX_RANGE = 2000000;       // guard: cap a single scan's span (2M seeds)

    // ---- Chain registry --------------------------------------------------
    // kind: 'p2pkh' (base58 P2PKH, one version byte, hash160 target),
    //       'zcash' (base58 P2PKH, two-byte version 0x1cb8),
    //       'evm'   (keccak-256 -> 0x address; all EVM chains share the format),
    //       'tron'  (keccak-256 + base58check 0x41),
    //       'xrp'   (hash160 + XRP base58 alphabet, version 0x00),
    //       'ed25519' (NOT derivable from a secp256k1 key).
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

    // ---- keccak-256 (Ethereum / TRON; verified against known vectors) ----
    var KECCAK_RC = [0x0000000000000001n, 0x0000000000008082n, 0x800000000000808an, 0x8000000080008000n, 0x000000000000808bn, 0x0000000080000001n, 0x8000000080008081n, 0x8000000000008009n, 0x000000000000008an, 0x0000000000000088n, 0x0000000080008009n, 0x000000008000000an, 0x000000008000808bn, 0x800000000000008bn, 0x8000000000008089n, 0x8000000000008003n, 0x8000000000008002n, 0x8000000000000080n, 0x000000000000800an, 0x800000008000000an, 0x8000000080008081n, 0x8000000000008080n, 0x0000000080000001n, 0x8000000080008008n];
    var KECCAK_RHO = [1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 2, 14, 27, 41, 56, 8, 25, 43, 62, 18, 39, 61, 20, 44];
    var KECCAK_PILN = [10, 7, 11, 17, 18, 3, 5, 16, 8, 21, 24, 4, 15, 23, 19, 13, 12, 2, 20, 14, 22, 9, 6, 1];
    var M64 = (1n << 64n) - 1n;
    function kRol(x, s) { s = s % 64n; return s === 0n ? x : ((x << s) | (x >> (64n - s))) & M64; }
    function keccakF(a) {
        var B = new Array(25).fill(0n);
        var C = [0n, 0n, 0n, 0n, 0n];
        for (var round = 0; round < 24; round++) {
            for (var x = 0; x < 5; x++) C[x] = a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20];
            for (var x = 0; x < 5; x++) {
                var D = C[(x + 4) % 5] ^ kRol(C[(x + 1) % 5], 1n);
                for (var y = 0; y < 5; y++) a[x + 5 * y] ^= D;
            }
            var t = a[1];
            for (var x = 0; x < 24; x++) {
                var j = KECCAK_PILN[x];
                var v = a[j];
                a[j] = kRol(t, BigInt(KECCAK_RHO[x]));
                t = v;
            }
            for (var y = 0; y < 5; y++) {
                for (var x = 0; x < 5; x++) {
                    B[x + 5 * y] = a[x + 5 * y] ^ ((~a[(x + 1) % 5 + 5 * y]) & a[(x + 2) % 5 + 5 * y]);
                }
            }
            for (var i = 0; i < 25; i++) a[i] = B[i];
            a[0] ^= KECCAK_RC[round];
        }
    }
    // bytes -> keccak-256 hex (64 chars)
    function keccak256Hex(bytes) {
        var rate = 136;
        var st = new BigUint64Array(25);
        var buf = new Uint8Array(bytes);
        var full = Math.floor(buf.length / rate);
        for (var b = 0; b < full; b++) {
            for (var i = 0; i < rate / 8; i++) {
                var off = b * rate + i * 8;
                var lane = 0n;
                for (var k = 7; k >= 0; k--) lane = (lane << 8n) | BigInt(buf[off + k]);
                st[i] ^= lane;
            }
            keccakF(st);
        }
        var rem = buf.length - full * rate;
        var last = new Uint8Array(rate);
        last.set(buf.subarray(full * rate));
        last[rem] ^= 0x01;
        last[rate - 1] ^= 0x80;
        for (var i = 0; i < rate / 8; i++) {
            var off = i * 8;
            var lane = 0n;
            for (var k = 7; k >= 0; k--) lane = (lane << 8n) | BigInt(last[off + k]);
            st[i] ^= lane;
        }
        keccakF(st);
        var out = new Uint8Array(32);
        for (var i = 0; i < 4; i++) {
            var lane = st[i];
            for (var k = 0; k < 8; k++) { out[i * 8 + k] = Number(lane & 0xffn); lane >>= 8n; }
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
    // Base58Check decode -> {payload, checksumOk}. Throws on bad char / short.
    function b58checkDecode(s, alphabet) {
        const hex = b58decodeToHex(s.trim(), alphabet);
        if (hex.length < 10) throw new Error("Address too short");
        const payload = hex.slice(0, -8), checksum = hex.slice(-8);
        return { payload: payload, checksumOk: dblsha256(payload).slice(0, 8) === checksum };
    }
    function base58checkAddr(payloadHex) {
        return b58encode(payloadHex + dblsha256(payloadHex).slice(0, 8));
    }
    function addrFromPub(pubHex, version) {
        return base58checkAddr(version + hash160Hex(pubHex));
    }
    function privToWif(privHex, compressed) {
        const payload = "80" + privHex + (compressed ? "01" : "");
        return b58encode(payload + dblsha256(payload).slice(0, 8));
    }

    // ---- secp256k1 (Jacobian scalar-mul: one inversion per multiply) -----
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

    // ---- Modeled BitcoinJS SecureRandom derivation -----------------------
    const LCG_A = 1664525, LCG_C = 1013904223; // Numerical Recipes — V8-era Math.random
    function randPool(seed) {
        const pool = new Uint8Array(256);
        let v = seed >>> 0;
        const draws = [v];
        for (let i = 1; i < 4; i++) { v = (Math.imul(v, LCG_A) + LCG_C) >>> 0; draws.push(v); }
        for (let d = 0; d < 4; d++) {
            pool[d * 4 + 0] = (draws[d] >>> 24) & 0xff;
            pool[d * 4 + 1] = (draws[d] >>> 16) & 0xff;
            pool[d * 4 + 2] = (draws[d] >>> 8) & 0xff;
            pool[d * 4 + 3] = draws[d] & 0xff;
        }
        for (let i = 16; i < 256; i++) {
            pool[i] = (pool[i - 16] ^ pool[i - 3] ^ ((i * 0x9e) & 0xff)) & 0xff;
        }
        return pool;
    }
    function rc4Bytes(key, n) {
        const S = new Uint8Array(256);
        for (let i = 0; i < 256; i++) S[i] = i;
        let j = 0;
        for (let i = 0; i < 256; i++) {
            j = (j + S[i] + key[i % key.length]) & 0xff;
            const t = S[i]; S[i] = S[j]; S[j] = t;
        }
        const out = new Uint8Array(n);
        let i = 0; j = 0;
        for (let k = 0; k < n; k++) {
            i = (i + 1) & 0xff;
            j = (j + S[i]) & 0xff;
            const t = S[i]; S[i] = S[j]; S[j] = t;
            out[k] = S[(S[i] + S[j]) & 0xff];
        }
        return out;
    }
    function deriveRandstormPriv(seed) {
        const bytes = rc4Bytes(randPool(seed), 32);
        let d = BigInt("0x" + bytesToHex(bytes)) % N;
        if (d === 0n) d = 1n;
        return d;
    }
    function pubsFromPriv(d) {
        const Q = sMul(d);
        const x = hx64(Q.x), y = hx64(Q.y);
        return { x: x, y: y, cpub: (Q.y & 1n ? "03" : "02") + x, upub: "04" + x + y };
    }

    // ---- Multi-chain address derivation ----------------------------------
    // Returns an array of address strings for the chain (P2PKH chains yield
    // both the compressed and uncompressed P2PKH variants; single-address
    // chains yield one).
    function chainAddresses(pk, c) {
        var info = chainInfo(c);
        if (info.kind === 'p2pkh') {
            return [addrFromPub(pk.cpub, info.version), addrFromPub(pk.upub, info.version)];
        }
        if (info.kind === 'zcash') {
            return [addrFromPub(pk.cpub, info.version), addrFromPub(pk.upub, info.version)];
        }
        if (info.kind === 'evm' || info.kind === 'tron') {
            var k = keccak256Hex(hexToBytes(pk.upub.slice(2))).slice(-40);
            if (info.kind === 'tron') return [base58checkAddr("41" + k)];
            return ["0x" + k.toLowerCase()];
        }
        if (info.kind === 'xrp') {
            return [base58checkAddrXrp("00" + hash160Hex(pk.cpub))];
        }
        return [];
    }
    function base58checkAddrXrp(payloadHex) {
        return b58encode(payloadHex + dblsha256(payloadHex).slice(0, 8), XRP_ALPHABET);
    }

    // Parse + validate a target address for a chain. Returns {ok, hash?, addr?,
    // target?} where `target` is what a candidate key's derived value is
    // compared against inside the worker, or {error} on failure. Throws on
    // invalid input so the caller can show the message.
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
        // base58 family: p2pkh / zcash / tron / xrp
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

    // ---- Bounded brute (Web Worker; Jacobian + CryptoJS + keccak in-worker) --
    // Message in : {target, kind, lo, hi}. Out: {type:'progress'|'found'|'done'}.
    function randWorkerBody() {
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
        function randPool(seed) {
            var pool = new Uint8Array(256), v = seed >>> 0, draws = [v], i, d;
            for (i = 1; i < 4; i++) { v = (Math.imul(v, 1664525) + 1013904223) >>> 0; draws.push(v); }
            for (d = 0; d < 4; d++) {
                pool[d * 4 + 0] = (draws[d] >>> 24) & 0xff;
                pool[d * 4 + 1] = (draws[d] >>> 16) & 0xff;
                pool[d * 4 + 2] = (draws[d] >>> 8) & 0xff;
                pool[d * 4 + 3] = draws[d] & 0xff;
            }
            for (i = 16; i < 256; i++) pool[i] = (pool[i - 16] ^ pool[i - 3] ^ ((i * 0x9e) & 0xff)) & 0xff;
            return pool;
        }
        function rc4Bytes(key, n) {
            var S = new Uint8Array(256), i, j = 0, t, k;
            for (i = 0; i < 256; i++) S[i] = i;
            for (i = 0; i < 256; i++) {
                j = (j + S[i] + key[i % key.length]) & 0xff;
                t = S[i]; S[i] = S[j]; S[j] = t;
            }
            var out = new Uint8Array(n);
            i = 0; j = 0;
            for (k = 0; k < n; k++) {
                i = (i + 1) & 0xff;
                j = (j + S[i]) & 0xff;
                t = S[i]; S[i] = S[j]; S[j] = t;
                out[k] = S[(S[i] + S[j]) & 0xff];
            }
            return out;
        }
        function derive(seed) {
            var bytes = rc4Bytes(randPool(seed), 32), hex = "";
            for (var i = 0; i < bytes.length; i++) hex += bytes[i].toString(16).padStart(2, "0");
            var d = BigInt("0x" + hex) % N;
            return d === 0n ? 1n : d;
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
            var out = new Uint8Array(32), o = 0;
            for (i = 0; i < 4; i++) {
                lane = st[i];
                for (k = 0; k < 8; k++) { out[o++] = Number(lane & 0xffn); lane >>= 8n; }
            }
            var hex = "";
            for (i = 0; i < out.length; i++) hex += out[i].toString(16).padStart(2, "0");
            return hex;
        }
        // candidate key -> compare value for the chain kind
        function compareValue(Q, kind) {
            var xh = hx(Q.x), yh = hx(Q.y);
            var cpub = (Q.y & 1n ? "03" : "02") + xh;
            var upub = "04" + xh + yh;
            if (kind === 'evm') return "0x" + keccak(bytesOfHex(upub.slice(2))).slice(-40);
            if (kind === 'tron') return keccak(bytesOfHex(upub.slice(2))).slice(-40);
            if (kind === 'xrp') return h160(cpub);
            return h160(cpub);   // p2pkh / zcash: hash160 target
        }
        function bytesOfHex(h) {
            var out = new Uint8Array(h.length / 2);
            for (var i = 0; i < out.length; i++) out[i] = parseInt(h.substring(i * 2, i * 2 + 2), 16);
            return out;
        }

        onmessage = function (e) {
            var lo = e.data.lo, hi = e.data.hi;
            var target = (e.data.target || "").toLowerCase();
            var kind = e.data.kind || 'p2pkh';
            var checked = 0, total = (hi - lo + 1);
            var wantUpub = (kind === 'p2pkh' || kind === 'zcash');
            for (var seed = lo; seed <= hi; seed++) {
                var d = derive(seed), Q = sMul(d);
                if (!Q) { checked++; continue; }
                var xh = hx(Q.x), cpub = (Q.y & 1n ? "03" : "02") + xh;
                if (wantUpub) {
                    if (h160(cpub) === target || h160("04" + xh + hx(Q.y)) === target) {
                        postMessage({ type: "found", seed: seed, priv: hx(d), format: h160(cpub) === target ? "compressed" : "uncompressed" });
                        return;
                    }
                } else {
                    var cv = compareValue(Q, kind);
                    if (cv === target) { postMessage({ type: "found", seed: seed, priv: hx(d), format: "chain" }); return; }
                }
                checked++;
                if ((seed & 1023) === 0) postMessage({ type: "progress", checked: checked, total: total, seed: seed });
            }
            postMessage({ type: "done", checked: checked });
        };
    }

    var WORKER_SRC = '(' + randWorkerBody.toString() + ')()';
    var _workerURL = null;
    function buildWorker() {
        try {
            if (typeof Worker === 'undefined' || typeof URL === 'undefined' || !URL.createObjectURL) return null;
            if (!_workerURL) _workerURL = URL.createObjectURL(new Blob([WORKER_SRC], { type: 'application/javascript' }));
            return new Worker(_workerURL);
        } catch (e) { return null; }
    }

    // Main-thread comparison for a candidate key (shared by verify + fallback).
    function compareKeyForChain(d, chain, target) {
        var pk = pubsFromPriv(d);
        var info = chainInfo(chain);
        if (info.kind === 'p2pkh' || info.kind === 'zcash') {
            if (hash160Hex(pk.cpub) === target) return { format: "compressed" };
            if (hash160Hex(pk.upub) === target) return { format: "uncompressed" };
            return null;
        }
        var cv = chainCompareValue(pk, chain);
        return cv === target ? { format: "chain" } : null;
    }
    function chainCompareValue(pk, chain) {
        var info = chainInfo(chain);
        if (info.kind === 'evm') return "0x" + keccak256Hex(hexToBytes(pk.upub.slice(2))).slice(-40);
        if (info.kind === 'tron') return keccak256Hex(hexToBytes(pk.upub.slice(2))).slice(-40);
        if (info.kind === 'xrp') return hash160Hex(pk.cpub);
        return hash160Hex(pk.cpub);
    }

    // Chunked main-thread fallback (worker unavailable / CDN import blocked).
    function mainThreadScan(chain, target, lo, hi, onProgress) {
        return new Promise(function (resolve) {
            let seed = lo, checked = 0; const total = (hi - lo + 1);
            function chunk() {
                const end = Math.min(hi, seed + 399);
                for (; seed <= end; seed++) {
                    const d = deriveRandstormPriv(seed), m = compareKeyForChain(d, chain, target);
                    if (m) { resolve({ found: true, seed: seed, priv: hx64(d), format: m.format }); return; }
                    checked++;
                }
                if (onProgress) onProgress({ checked: checked, total: total, seed: end });
                if (seed <= hi) setTimeout(chunk, 0); else resolve({ found: false, checked: checked });
            }
            chunk();
        });
    }

    function runScan(chain, target, kind, lo, hi, onProgress) {
        return new Promise(function (resolve) {
            const w = buildWorker();
            if (!w) { mainThreadScan(chain, target, lo, hi, onProgress).then(resolve); return; }
            let fellBack = false;
            const fallback = function () { if (fellBack) return; fellBack = true; try { w.terminate(); } catch (e) { } mainThreadScan(chain, target, lo, hi, onProgress).then(resolve); };
            w.onmessage = function (ev) {
                const m = ev.data;
                if (m.type === 'noimport') { fallback(); }
                else if (m.type === 'progress') { if (onProgress) onProgress(m); }
                else if (m.type === 'found') { try { w.terminate(); } catch (e) { } resolve({ found: true, seed: m.seed, priv: m.priv, format: m.format }); }
                else if (m.type === 'done') { try { w.terminate(); } catch (e) { } resolve({ found: false, checked: m.checked }); }
            };
            w.onerror = function () { fallback(); };
            w.postMessage({ target: target, kind: kind, lo: lo, hi: hi });
        });
    }

    // ---- Output header + export ------------------------------------------
    function getOutputHeader(elementId) {
        let header = `<div class="result-header">CRYPTOGRAPHYTUBE<span class="tool-tag">Randstorm Seed Scan</span></div>`;
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
    function keyBlock(seed, d, chain, matchedFormat) {
        const pk = pubsFromPriv(d);
        const priv = hx64(d);
        const info = chainInfo(chain);
        let h = '';
        h += '<div class="rsz-vuln-box">';
        h += '<div class="rsz-vuln-title"><img src="../assets/svgs/solid/triangle-exclamation.svg" width="15" height="15" alt=""> ' +
            'WEAK KEY — SecureRandom seed ' + seed + ' · ' + escapeHtml(info.name) +
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
            h += '<div class="rsz-leak-bits">Recovered by scanning the seed range — the address regenerates from this key (' +
                escapeHtml(matchedFormat) + (matchedFormat === 'chain' ? ' address' : ' P2PKH') +
                '), so the match is verified, not guessed.</div>';
        }
        h += '</div>';
        return h;
    }

    function renderScanResult(res, lo, hi, targetAddr, chain) {
        const info = chainInfo(chain);
        let html = '';
        html += '<div class="rsz-summary">';
        html += '<span class="rsz-chip">' + escapeHtml(info.name) + '</span>';
        html += '<span class="rsz-chip">seed range ' + lo + '–' + hi + '</span>';
        html += '<span class="rsz-chip">' + (res.checked != null ? res.checked.toLocaleString() : (hi - lo + 1).toLocaleString()) + ' seeds tested</span>';
        if (res.found) html += '<span class="rsz-chip rsz-chip-danger">Weak key recovered</span>';
        else html += '<span class="rsz-chip rsz-chip-ok">No weak key in range</span>';
        html += '</div>';
        html += '<div class="rsz-line"><span class="rsz-tag">TARGET</span>' +
            '<code class="rsz-val rsz-addr-val">' + escapeHtml(targetAddr) + '</code>' + copyBtn(targetAddr) + '</div>';
        if (res.found) {
            html += keyBlock(res.seed, BigInt('0x' + res.priv), chain, res.format);
        } else {
            html += '<div class="rsz-leak-note rsz-leak-ok">Scanned ' + (hi - lo + 1).toLocaleString() +
                ' seeds for a ' + escapeHtml(info.name) + ' address — no seed in this range produced it. ' +
                'It may use a seed outside the range, or was not generated under the modeled Randstorm collapse. ' +
                'Widen the range (the full 2011–2015 space is ~2^32 seeds) or try another slice.</div>';
        }
        return html;
    }

    function renderVerify(seed, chain) {
        const info = chainInfo(chain);
        let html = '';
        html += '<div class="rsz-summary">';
        html += '<span class="rsz-chip">seed ' + seed + '</span>';
        html += '<span class="rsz-chip rsz-chip-danger">1 key derived</span>';
        html += '</div>';
        html += '<div class="rsz-leak-note">A collapsed SecureRandom pool turns this single 32-bit seed into a fully-determined key. ' +
            'Paste the ' + escapeHtml(info.name) + ' address below into <strong>Scan</strong> to watch the seed range brute recover it.</div>';
        html += keyBlock(seed, deriveRandstormPriv(seed), chain, null);
        return html;
    }

    // ---- Entry points ----------------------------------------------------
    function activeChain() {
        return window.TXR_CHAIN || 'bitcoin';
    }
    function readRange() {
        const loEl = document.getElementById('range_lo');
        const hiEl = document.getElementById('range_hi');
        let lo = loEl ? parseInt(loEl.value, 10) : 0;
        let hi = hiEl ? parseInt(hiEl.value, 10) : 65535;
        if (!Number.isFinite(lo) || lo < 0) lo = 0;
        if (!Number.isFinite(hi) || hi < 0) hi = 65535;
        if (hi < lo) { const t = lo; lo = hi; hi = t; }
        if (hi - lo > MAX_RANGE) hi = lo + MAX_RANGE;
        return { lo: lo, hi: hi };
    }

    // Scan a target address across a seed range (bounded brute) on the active chain.
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

        const { lo, hi } = readRange();
        const t0 = Date.now();
        const setStatus = function (msg) { out.innerHTML = header + '<div class="rsz-status">' + spinner(14) + ' ' + escapeHtml(msg) + '</div>'; };
        setStatus('Scanning seeds ' + lo + '–' + hi + ' for a ' + info.name + ' address (' + addr + ')…');

        const res = await runScan(chain, target.target, target.kind, lo, hi, function (p) {
            const pct = p.total ? Math.floor((p.checked / p.total) * 100) : 0;
            setStatus('Scanning… seed ' + (p.seed != null ? p.seed : '?') + ' / ' + hi + '  (' + pct + '%, ' + p.checked.toLocaleString() + ' seeds)');
        });
        res._ms = Date.now() - t0;
        out.innerHTML = header + renderScanResult(res, lo, hi, target.addr, chain) +
            '<div class="rsz-leak-note" style="margin-top:.6rem">Scan finished in ' + (res._ms / 1000).toFixed(1) + ' s.</div>';
    }

    // Verify a single seed (instant, main thread) on the active chain.
    function verifyPid() {
        const out = document.getElementById("out_txid");
        if (!out) return;
        const header = getOutputHeader(out.id);
        const chain = activeChain();
        const raw = (document.getElementById('seed_input') || {}).value;
        const seed = parseInt((raw || "").trim(), 10);
        if (!Number.isFinite(seed) || seed < 0 || seed > 0xFFFFFFFF) {
            out.innerHTML = header + '<div class="rsz-error"><img src="../assets/svgs/solid/triangle-exclamation.svg" width="14" height="14" alt=""> Enter a 32-bit seed (0 to 4294967295, e.g. 1337).</div>';
            return;
        }
        out.innerHTML = header + renderVerify(seed >>> 0, chain);
    }

    // ---- Expose ----------------------------------------------------------
    window.processTxid = processTxid;   // Scan
    window.verifyPid = verifyPid;       // Verify a seed
    window.exportOne = exportOne;
})();
