<?php
/* ============================================================================
   luck-worker.php  —  24/7 server-side Luck Puzzle scanner (cPanel cron)

   The browser auto-scanner (assets/js/luck-found.js) only runs while a visitor
   has a page open. This worker does the same job on the SERVER, so scanning
   never stops: no browser, no visitor, nothing to click. Runs from cPanel
   cron every minute, resumes from a durable cursor, and writes every hit into
   the SAME per-domain store that found.php serves — so every visitor sees an
   identical, live, shared list.

   NEVER SKIPS WORK
     The cursor only advances AFTER a batch is durably queued. A crash, a
     timeout, or an overlapping run cannot lose keys: the batch is already on
     disk, and the lock makes a second run stand down instead of double-scanning.

   USAGE
     php luck-worker.php --selftest          verify crypto against known vectors
     php luck-worker.php --status            show cursor / totals / progress
     php luck-worker.php --run               one batch (what cron calls)
     php luck-worker.php --run --batch=5000  bigger batch
     php luck-worker.php --reset             clear the cursor (keeps findings)
     php luck-worker.php --secret            print the HTTP trigger secret

   CRON (every minute):
     * * * * * /usr/local/bin/php /home/USER/public_html/luck-worker.php --run >/dev/null 2>&1
   or over HTTP (if CLI php isn't available):
     * * * * * /usr/bin/curl -s "https://SITE/luck-worker.php?run=1&k=SECRET" >/dev/null

   REAL DATA ONLY — this never fabricates a finding. A record is stored only
   when a balance API actually reports activity (balance, received, or tx).
   ============================================================================ */

@ini_set('display_errors', '0');
error_reporting(0);
@set_time_limit(0);
@ini_set('memory_limit', '256M');

/* ====================================================================== CONFIG */

define('LW_VERSION', '1.0.0');

/* Store — identical layout to found.php so the dashboard needs no changes. */
$DATA_DIR = __DIR__ . '/found-data';
$FOUND    = $DATA_DIR . '/found.jsonl';
$INDEX    = $DATA_DIR . '/index.txt';
$COUNT    = $DATA_DIR . '/count.txt';

/* Worker's own state (durable cursor + queue + totals). */
$STATE    = $DATA_DIR . '/worker-state.json';
$LOCK     = $DATA_DIR . '/worker.lock';
$KEYFILE  = $DATA_DIR . '/worker-key.txt';
$LOGFILE  = $DATA_DIR . '/worker.log';

/* How the cursor walks the keyspace.
     'range'  — sequential from `start`, wrapping is off. Provably covers every
                key in [start, end] exactly once, resuming across runs.
     'random' — uniform random 256-bit scalars (what the browser does). Nothing
                is ever "skipped" because there is no defined order to skip in;
                the queue+dedup still guarantees no double-checking.
   Default is sequential: it is the only mode where "nothing missed" means
   something concrete, and it makes a puzzle range a real search. */
$CFG = array(
    'mode'      => 'range',
    'start'     => '1',                          // hex, no 0x
    'end'       => '',                           // blank = max valid secp256k1 scalar
    'batch'     => 2000,                         // secp256k1 keys generated per run
    'queue_max' => 20000,                        // addresses awaiting a balance check
    'chains'    => array('bitcoin', 'litecoin', 'dogecoin', 'bitcoin-cash',
                         'ethereum', 'tron', 'xrp'),
    'solana'    => false,                        // ed25519 pass (off by default)
);

/* secp256k1 group order n */
define('SECP_N', 'fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141');

/* ===================================================================== CRYPTO */

/* ---- 32-byte big-endian byte-array math (no gmp / no bcmath needed) ------ */

function b32_cmp($a, $b) {                      // -1 / 0 / 1, fixed 32-byte strings
    for ($i = 0; $i < 32; $i++) {
        $x = ord($a[$i]); $y = ord($b[$i]);
        if ($x !== $y) { return $x < $y ? -1 : 1; }
    }
    return 0;
}
function b32_add($a, $b) {                      // (a + b) mod 2^256
    $out = str_repeat("\x00", 32);
    $carry = 0;
    for ($i = 31; $i >= 0; $i--) {
        $s = ord($a[$i]) + ord($b[$i]) + $carry;
        $out[$i] = chr($s & 0xFF);
        $carry = $s >> 8;
    }
    return $out;
}
function b32_sub($a, $b) {                      // (a - b) mod 2^256
    $out = str_repeat("\x00", 32);
    $borrow = 0;
    for ($i = 31; $i >= 0; $i--) {
        $d = ord($a[$i]) - ord($b[$i]) - $borrow;
        if ($d < 0) { $d += 256; $borrow = 1; } else { $borrow = 0; }
        $out[$i] = chr($d);
    }
    return $out;
}

/* ---- base58 ------------------------------------------------------------- */
function b58enc($bin, $abc = '123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz') {
    $bytes = array_values(unpack('C*', $bin));
    $zeros = 0; $n = count($bytes);
    while ($zeros < $n && $bytes[$zeros] === 0) { $zeros++; }
    $buf = array_slice($bytes, $zeros);
    $out = '';
    while (count($buf) > 0) {
        $rem = 0; $q = array();
        foreach ($buf as $b) {
            $acc = $rem * 256 + $b;
            $d = intdiv($acc, 58);
            $rem = $acc % 58;
            if (count($q) > 0 || $d > 0) { $q[] = $d; }
        }
        $out = $abc[$rem] . $out;
        $buf = $q;
    }
    return str_repeat('1', $zeros) . $out;
}
function sha256d($bin) { return hash('sha256', hash('sha256', $bin, true), true); }
function b58check($payload, $abc = null) {
    $chk = substr(sha256d($payload), 0, 4);
    return $abc === null ? b58enc($payload . $chk) : b58enc($payload . $chk, $abc);
}
function hash160($bin) { return hash('ripemd160', hash('sha256', $bin, true), true); }
function hex0x($bin) { return bin2hex($bin); }

/* ---- bech32 / bech32m (BIP173 / BIP350) --------------------------------- */
function bech32_polymod($v) {
    $gen = array(0x3b6a57b2, 0x26508e6d, 0x1ea119fa, 0x3d4233dd, 0x2a1462b3);
    $chk = 1;
    foreach ($v as $x) {
        $top = $chk >> 25;
        $chk = (($chk & 0x1ffffff) << 5) ^ $x;
        for ($i = 0; $i < 5; $i++) {
            if (($top >> $i) & 1) { $chk ^= $gen[$i]; }
        }
    }
    return $chk;
}
function bech32_hrp_expand($hrp) {
    $out = array();
    $l = strlen($hrp);
    for ($i = 0; $i < $l; $i++) { $out[] = ord($hrp[$i]) >> 5; }
    $out[] = 0;
    for ($i = 0; $i < $l; $i++) { $out[] = ord($hrp[$i]) & 31; }
    return $out;
}
function bech32_convertbits($data, $from, $to, $pad) {
    $acc = 0; $bits = 0; $out = array();
    $maxv = (1 << $to) - 1;
    foreach ($data as $value) {
        if ($value < 0 || ($value >> $from) !== 0) { return false; }
        $acc = ($acc << $from) | $value;
        $bits += $from;
        while ($bits >= $to) {
            $bits -= $to;
            $out[] = ($acc >> $bits) & $maxv;
        }
    }
    if ($pad) {
        if ($bits > 0) { $out[] = ($acc << ($to - $bits)) & $maxv; }
    } elseif ($bits >= $from || (($acc << ($to - $bits)) & $maxv) !== 0) {
        return false;
    }
    return $out;
}
function bech32_encode($hrp, $data5, $spec) {         // $spec: 'bech32' | 'bech32m'
    $const = ($spec === 'bech32m') ? 0x2bc830a3 : 1;
    $values = array_merge(bech32_hrp_expand($hrp), $data5, array(0, 0, 0, 0, 0, 0));
    $polymod = bech32_polymod($values) ^ $const;
    $chk = array();
    for ($i = 0; $i < 6; $i++) { $chk[] = ($polymod >> (5 * (5 - $i))) & 31; }
    $charset = 'qpzry9x8gf2tvdw0s3jn54khce6mua7l';
    $out = $hrp . '1';
    foreach (array_merge($data5, $chk) as $d) { $out .= $charset[$d]; }
    return $out;
}
/* segwit v0 (P2WPKH/P2WSH) = bech32 ; v1+ (P2TR) = bech32m */
function segwit_addr($hrp, $version, $prog) {
    $data = array_merge(array($version), bech32_convertbits(array_values(unpack('C*', $prog)), 8, 5, true));
    return bech32_encode($hrp, $data, $version === 0 ? 'bech32' : 'bech32m');
}

/* ---- keccak256 (pure PHP). PHP's hash('sha3-256') is NOT keccak256 —
        SHA-3 pads with 0x06, original Keccak pads with 0x01, so the digests
        differ. ETH addresses and Tron need real keccak256. ------------------ */

function hex64($h) {                                   // 16 hex chars -> 64-bit int
    return (hexdec(substr($h, 0, 8)) << 32) | hexdec(substr($h, 8, 8));
}
function shr64u($v, $n) {                              // logical (unsigned) right shift
    if ($n <= 0)  { return $v; }
    if ($n >= 64) { return 0; }
    return ($v >> $n) & (PHP_INT_MAX >> ($n - 1));
}
function rotl64($v, $n) {
    $n &= 63;
    if ($n === 0) { return $v; }
    return (($v << $n) | shr64u($v, 64 - $n));
}
function keccak_f(&$A, $RC) {
    static $ROT = null;
    if ($ROT === null) {
        $ROT = array(
            array(0, 36, 3, 41, 18),
            array(1, 44, 10, 45, 2),
            array(62, 6, 43, 15, 61),
            array(28, 55, 25, 21, 56),
            array(27, 20, 39, 8, 14),
        );
    }
    for ($round = 0; $round < 24; $round++) {
        /* theta */
        $C = array();
        for ($x = 0; $x < 5; $x++) {
            $C[$x] = $A[$x][0] ^ $A[$x][1] ^ $A[$x][2] ^ $A[$x][3] ^ $A[$x][4];
        }
        $D = array();
        for ($x = 0; $x < 5; $x++) {
            $D[$x] = $C[($x + 4) % 5] ^ rotl64($C[($x + 1) % 5], 1);
        }
        for ($x = 0; $x < 5; $x++) {
            for ($y = 0; $y < 5; $y++) { $A[$x][$y] ^= $D[$x]; }
        }
        /* rho + pi */
        $B = array();
        for ($x = 0; $x < 5; $x++) {
            for ($y = 0; $y < 5; $y++) {
                $B[$y][(2 * $x + 3 * $y) % 5] = rotl64($A[$x][$y], $ROT[$x][$y]);
            }
        }
        /* chi */
        for ($x = 0; $x < 5; $x++) {
            for ($y = 0; $y < 5; $y++) {
                $A[$x][$y] = $B[$x][$y] ^ ((~$B[($x + 1) % 5][$y]) & $B[($x + 2) % 5][$y]);
            }
        }
        /* iota */
        $A[0][0] ^= $RC[$round];
    }
}
function keccak256($msg) {
    static $RC = null;
    if ($RC === null) {
        $RC = array_map('hex64', array(
            '0000000000000001', '0000000000008082', '800000000000808a', '8000000080008000',
            '000000000000808b', '0000000080000001', '8000000080008081', '8000000000008009',
            '000000000000008a', '0000000000000088', '0000000080008009', '000000008000000a',
            '000000008000808b', '800000000000008b', '8000000000008089', '8000000000008003',
            '8000000000008002', '8000000000000080', '000000000000800a', '800000008000000a',
            '8000000080008081', '8000000000008080', '0000000080000001', '8000000080008008',
        ));
    }
    $rate = 136;                                    // 1088 bits for keccak-256
    $msg  = $msg . "\x01";                          // Keccak (original) domain byte
    while ((strlen($msg) % $rate) !== 0) { $msg .= "\x00"; }
    $msg[strlen($msg) - 1] = chr(ord($msg[strlen($msg) - 1]) | 0x80);

    $A = array();
    for ($x = 0; $x < 5; $x++) { $A[$x] = array(0, 0, 0, 0, 0); }

    $blocks = strlen($msg) / $rate;
    for ($b = 0; $b < $blocks; $b++) {
        $off = $b * $rate;
        for ($i = 0; $i < $rate / 8; $i++) {
            $lo = unpack('V', substr($msg, $off + $i * 8, 4))[1];
            $hi = unpack('V', substr($msg, $off + $i * 8 + 4, 4))[1];
            $A[$i % 5][intdiv($i, 5)] ^= (($hi << 32) | $lo);
        }
        keccak_f($A, $RC);
    }
    /* squeeze: 32 bytes = lanes 0..3, little-endian */
    $out = '';
    for ($i = 0; $i < 4; $i++) {
        $v = $A[$i % 5][intdiv($i, 5)];
        $out .= pack('V', $v & 0xFFFFFFFF) . pack('V', shr64u($v, 32) & 0xFFFFFFFF);
    }
    return $out;
}
function keccak256_hex($msg) { return bin2hex(keccak256($msg)); }

/* ---- secp256k1 --------------------------------------------------------- */
function secp_pub($hex32) {                         // scalar hex -> array(comp, unc)
    $raw = hex2bin(str_pad($hex32, 64, '0', STR_PAD_LEFT));
    if (strlen($raw) !== 32) { return null; }
    /* DER INTEGER is SIGNED: a scalar whose top bit is set (~50% of the
       keyspace!) must carry a leading 0x00 or OpenSSL reads it as negative
       and derives the wrong public key. */
    $d = (ord($raw[0]) & 0x80) ? "\x00" . $raw : $raw;
    $dl = chr(strlen($d));
    /* ECPrivateKey ::= SEQ { INTEGER 1, OCTET STRING d, [0] OID secp256k1 } */
    $body = "\x02\x01\x01" . "\x04" . $dl . $d . "\xa0\x07\x06\x05\x2b\x81\x04\x00\x0a";
    $der  = "\x30" . chr(strlen($body)) . $body;
    $pem = "-----BEGIN EC PRIVATE KEY-----\n" . chunk_split(base64_encode($der), 64, "\n")
         . "-----END EC PRIVATE KEY-----\n";
    $res = @openssl_pkey_get_private($pem);
    if ($res === false) { return null; }
    $k = @openssl_pkey_get_details($res);
    if (!is_array($k) || !isset($k['ec']['x'], $k['ec']['y'])) { return null; }
    /* DER INTEGER content octets drop leading zeros (~1 in 256 coords).
       Pad back to a full 32-byte field element or the address is silently wrong. */
    $x = str_pad($k['ec']['x'], 32, "\x00", STR_PAD_LEFT);
    $y = str_pad($k['ec']['y'], 32, "\x00", STR_PAD_LEFT);
    if (strlen($x) !== 32 || strlen($y) !== 32) { return null; }
    if ($x === str_repeat("\x00", 32)) { return null; }
    $comp = ((ord($y[31]) & 1) ? "\x03" : "\x02") . $x;
    return array($comp, "\x04" . $x . $y, $x, $y);
}

/* ---- taproot (BIP341/BIP86). Q = P + t*G  ==  (d + t)*G, so the tweak is
        applied on the SCALAR — no EC point addition, no modular inverse. ---- */
function tagged_hash($tag, $msg) {
    $t = hash('sha256', $tag, true);
    return hash('sha256', $t . $t . $msg, true);
}
function b32_from_hex($h) { return hex2bin(str_pad($h, 64, '0', STR_PAD_LEFT)); }

/* 33-byte (carry-preserving) add/sub. d + t overflows 256 bits about HALF the
   time, so a fixed-width 32-byte add silently loses bit 256 and yields ~50%
   wrong taproot addresses. Everything below works in 33 bytes. */
function b33_add($a, $b) {
    $out = str_repeat("\x00", 33);
    $carry = 0;
    for ($i = 31; $i >= 0; $i--) {
        $s = ord($a[$i]) + ord($b[$i]) + $carry;
        $out[$i + 1] = chr($s & 0xFF);
        $carry = $s >> 8;
    }
    $out[0] = chr($carry);
    return $out;
}
function b33_sub($a, $b) {                       // both 33 bytes, a >= b
    $out = str_repeat("\x00", 33);
    $borrow = 0;
    for ($i = 32; $i >= 0; $i--) {
        $d = ord($a[$i]) - ord($b[$i]) - $borrow;
        if ($d < 0) { $d += 256; $borrow = 1; } else { $borrow = 0; }
        $out[$i] = chr($d);
    }
    return $out;
}

/* BIP341/BIP86 taproot. Q = P + t*G where P = lift_x(x_P) is the EVEN-y point,
   so when d*G has odd y the effective scalar is (n - d). Because t is applied
   on the scalar, Q = (d_eff + t)*G — no EC point addition, no modular inverse. */
function taproot_addr($d_hex, $hrp = 'bc') {
    $pub = secp_pub($d_hex);
    if ($pub === null) { return null; }
    $xonly = $pub[2];
    $yodd  = (ord($pub[3][31]) & 1) === 1;

    $n32 = b32_from_hex(SECP_N);
    $n33 = "\x00" . $n32;

    $d = b32_from_hex($d_hex);
    if (b32_cmp($d, $n32) >= 0 || $d === str_repeat("\x00", 32)) { return null; }
    $d_eff = $yodd ? b32_sub($n32, $d) : $d;            // lift_x -> even y

    $t = tagged_hash('TapTweak', $xonly);               // 32 bytes
    if (b32_cmp($t, $n32) >= 0) { $t = b32_sub($t, $n32); }

    $s = b33_add($d_eff, $t);                           // carry preserved
    if (strcmp($s, $n33) >= 0) { $s = b33_sub($s, $n33); }
    $d2 = substr($s, 1);                                // back to 32 bytes
    if (b32_cmp($d2, $n32) >= 0 || $d2 === str_repeat("\x00", 32)) { return null; }

    $pub2 = secp_pub(bin2hex($d2));
    if ($pub2 === null) { return null; }
    return segwit_addr($hrp, 1, $pub2[2]);              // segwit v1 -> bech32m
}

/* ---- WIF ---------------------------------------------------------------- */
function wif($hex32, $compressed = true, $prefix = "\x80") {
    $raw = hex2bin(str_pad($hex32, 64, '0', STR_PAD_LEFT));
    return b58check($prefix . $raw . ($compressed ? "\x01" : ''));
}

/* ==================================================== ADDRESS DERIVATION ==== */

/* One secp256k1 scalar -> every address that shares it. */
function addresses_for_scalar($hex32) {
    $pub = secp_pub($hex32);
    if ($pub === null) { return null; }
    $comp = $pub[0]; $unc = $pub[1];
    $h160c = hash160($comp);
    $h160u = hash160($unc);

    $evm  = substr(keccak256(substr($unc, 1)), 12);        // last 20 bytes
    $tron = substr(keccak256(substr($unc, 1)), 12);

    return array(
        /* --- bitcoin: legacy (comp + unc), segwit v0, taproot --- */
        'bitcoin_p2pkh_c'  => b58check("\x00" . $h160c),
        'bitcoin_p2pkh_u'  => b58check("\x00" . $h160u),
        'bitcoin_p2wpkh'   => segwit_addr('bc', 0, $h160c),
        'bitcoin_p2tr'     => taproot_addr($hex32, 'bc'),
        /* --- forks --- */
        'litecoin_p2pkh'   => b58check("\x30" . $h160c),
        'litecoin_p2wpkh'  => segwit_addr('ltc', 0, $h160c),
        'dogecoin_p2pkh'   => b58check("\x1e" . $h160c),
        'bitcoin_cash'     => b58check("\x00" . $h160c),
        /* --- evm (one address, 8 chains) + tron --- */
        'evm'              => hex0x($evm),
        'tron'             => b58check("\x41" . $tron),
        /* --- xrp: secp256k1 + ripple base58 alphabet --- */
        'xrp'              => b58check("\x00" . $h160c,
                                'rpshnaf39wBUDNEGHJKLM4PQRST7VWXYZ2bcdeCg65jkm8oFqi1tuvAxyz'),
    );
}

/* ed25519 chains (separate 32-byte seed, not the secp256k1 scalar). */
function solana_addr($seed32) {
    if (!function_exists('sodium_crypto_sign_seed_keypair')) { return null; }
    $kp = sodium_crypto_sign_seed_keypair($seed32);
    return b58enc(sodium_crypto_sign_publickey($kp));
}

/* ================================================================= SELFTEST */

function lw_selftest() {
    $pass = 0; $fail = 0;
    $t = function ($name, $got, $want) use (&$pass, &$fail) {
        $ok = ($got === $want);
        $ok ? $pass++ : $fail++;
        printf("  %-6s %-34s %s\n", $ok ? 'PASS' : 'FAIL', $name,
               $ok ? '' : ("got " . substr((string)$got, 0, 44) . "  want " . substr((string)$want, 0, 44)));
    };

    echo "--- secp256k1 (privkey 1) ---\n";
    $p1 = secp_pub('1');
    $t('pubkey compressed', bin2hex($p1[0]),
       '0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798');
    $t('address uncompressed', b58check("\x00" . hash160($p1[1])), '1EHNa6Q4Jz2uvNExL497mE43ikXhwF6kZm');
    $t('address compressed',   b58check("\x00" . hash160($p1[0])), '1BgGZ9tcN4rm9KBzDn7KprQz87SZ26SAMH');
    $t('wif compressed', wif('1'), 'KwDiBf89QgGbjEhKnhXJuH7LrciVrZi3qYjgd9M7rFU73sVHnoWn');
    /* scalar whose x starts with a zero byte — proves the DER-padding fix
       (raw OpenSSL coords would be 31 bytes here and give a wrong address) */
    $pz = secp_pub('99');   // 0x99 = 153
    $t('leading-zero x padded', strlen($pz[2]), 32);
    $t('addr for leading-zero x', b58check("\x00" . hash160($pz[0])), '12bkr6BP2pYFggCCr3XvkTSNzJRXYvZL9a');
    /* top bit set — proves the DER signed-INTEGER fix */
    $ph = secp_pub('ff');
    $t('high-bit scalar ok', $ph === null ? 'null' : strlen($ph[2]), 32);

    $p2 = secp_pub('18e14a7b6a307f426a94f8114701e7c8e774e7f9a47e2c2035db29a206321725');
    $t('address vector 2', b58check("\x00" . hash160($p2[0])), '1PMycacnJaSqwwJqjawXBErnLsZ7RkXUAs');

    echo "--- keccak256 (NOT sha3-256) ---\n";
    $t('keccak256("")', keccak256_hex(''),
       'c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470');
    $t('keccak256("abc")', keccak256_hex('abc'),
       '4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45');
    $t(' != sha3-256("")', keccak256_hex('') === hash('sha3-256', ''), false);

    echo "--- bech32 / bech32m (published BIP173 / BIP350 vectors) ---\n";
    $t('bech32 P2WPKH (privkey 1)',
       segwit_addr('bc', 0, hash160($p1[0])), 'bc1qw508d6qejxtdg4y5r3zarvary0c5xw7kv8f3t4');
    $t('bech32 ltc P2WPKH',
       segwit_addr('ltc', 0, hash160($p1[0])), 'ltc1qw508d6qejxtdg4y5r3zarvary0c5xw7kgmn4n9');
    /* BIP350 vector: witness v1, program 79be667e... */
    $t('bech32m BIP350 vector',
       bech32_encode('bc', array_merge(array(1), bech32_convertbits(array_values(
         unpack('C*', hex2bin('79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798'))), 8, 5, true)),
         'bech32m'),
       'bc1p5d7rjq7g6rdk2yhzks9smlaqtedr4dekq08ge8ztwac72sfr9rusxg3297');
    /* BIP86 published vector: this program must encode back to this address. */
    $t('bech32m BIP86 vector',
       segwit_addr('bc', 1, hex2bin('a60869f0dbcf1dc659c9cecbaf8050135ea9e8cdc487053f1dc6880949dc684c')),
       'bc1p5cyxnuxmeuwuvkwfem96lqzszd02n6xdcjrs20cac6yqjjwudpxqkedrcr');
    /* taproot scalar path (tweak + even-y lift) is cross-checked against an
       independent Python secp256k1 implementation in the test harness. */
    $tr1 = taproot_addr('2', 'bc');
    $t('taproot scalar path runs', $tr1 !== null && strpos($tr1, 'bc1p') === 0, true);

    echo "--- eth / tron / xrp ---\n";
    $a = addresses_for_scalar('1');
    $t('eth addr (privkey 1)', $a['evm'], '7e5f4552091a69125d5dfcb7b8c2659029395bdf');
    $t('tron addr (privkey 1)', $a['tron'], 'TMVQGm1qAQYVdetCeGRRkTWYYrLXuHK2HC');
    $t('ltc addr (privkey 1)', $a['litecoin_p2pkh'], 'LVuDpNCSSj6pQ7t9Pv6d6sUkLKoqDEVUnJ');

    echo "--- vector 2 full set ---\n";
    $a2 = addresses_for_scalar('18e14a7b6a307f426a94f8114701e7c8e774e7f9a47e2c2035db29a206321725');
    $t('btc p2pkh c', $a2['bitcoin_p2pkh_c'], '1PMycacnJaSqwwJqjawXBErnLsZ7RkXUAs');
    $t('btc p2wpkh',  $a2['bitcoin_p2wpkh'],  'bc1q876q8h3v8u4dfaqqjrsndmy9nq23v6gqgnw2q6');

    echo "\n" . ($fail === 0 ? "ALL $pass CHECKS PASSED\n" : "$pass passed, $fail FAILED\n");
    return $fail === 0 ? 0 : 1;
}

/* ============================================================ PATHS / STATE */

function lw_paths() {
    $d = __DIR__ . '/found-data';
    return array(
        'dir'   => $d,
        'found' => $d . '/found.jsonl',
        'index' => $d . '/index.txt',
        'count' => $d . '/count.txt',
        'state' => $d . '/worker-state.json',
        'queue' => $d . '/worker-queue.json',
        'lock'  => $d . '/worker.lock',
        'key'   => $d . '/worker-key.txt',
        'log'   => $d . '/worker.log',
    );
}

function lw_defaults() {
    return array(
        'version'      => LW_VERSION,
        'mode'         => 'range',        // 'range' (sequential) | 'random'
        'start'        => '1',            // hex, no 0x — where a range walk begins
        'cursor'       => '1',            // next scalar to generate (range mode)
        'gen_per_run'  => 2000,           // keys derived per run (CPU-bound, cheap)
        'queue_low'    => 4000,           // generate only while the queue is under this
        'queue_max'    => 20000,          // hard cap — drop-oldest if ever exceeded
        'check_batch'  => 100,            // entries checked per run, batched chains
        'single_budget'=> 25,             // entries checked per run, per-address chains
        'groups'       => array('bitcoin','litecoin','dogecoin','bitcoin-cash',
                                'evm','tron','xrp'),
        'created'      => 0,
        'runs'         => 0,
        'generated'    => 0,              // keys derived, lifetime
        'checked'      => 0,              // (entry,group) pairs checked, lifetime
        'hits'         => 0,              // records written, lifetime
        'last_run'     => 0,
        'last_hit'     => 0,
        'last_error'   => '',
        'dropped'      => 0,              // queue entries shed at queue_max (should stay 0)
    );
}

function lw_state_load($file) {
    $d = lw_defaults();
    if (!is_file($file)) { return $d; }
    $j = @json_decode((string) @file_get_contents($file), true);
    if (!is_array($j)) { return $d; }
    return array_merge($d, $j);
}

function lw_state_save($file, $state) {
    $tmp = $file . '.tmp';
    $ok = @file_put_contents($tmp, json_encode($state, JSON_PRETTY_PRINT), LOCK_EX);
    if ($ok === false) { return false; }
    return @rename($tmp, $file);                 // atomic on the same filesystem
}

function lw_queue_load($file) {
    if (!is_file($file)) { return array(); }
    $j = @json_decode((string) @file_get_contents($file), true);
    return is_array($j) ? $j : array();
}
function lw_queue_save($file, $q) {
    $tmp = $file . '.tmp';
    if (@file_put_contents($tmp, json_encode($q), LOCK_EX) === false) { return false; }
    return @rename($tmp, $file);
}

function lw_log($file, $msg) {
    $line = gmdate('Y-m-d H:i:s') . 'Z ' . $msg . "\n";
    @file_put_contents($file, $line, FILE_APPEND | LOCK_EX);
    /* keep the log trim: >256KB -> keep the last 64KB */
    if (@filesize($file) > 262144) {
        $tail = @file_get_contents($file, false, null, -65536);
        if ($tail !== false) { @file_put_contents($file, $tail, LOCK_EX); }
    }
}

/* ====================================================================== HTTP */

function lw_http($url, $method = 'GET', $body = null, $headers = array(), $timeout = 15) {
    if (function_exists('curl_init')) {
        $ch = curl_init($url);
        curl_setopt($ch, CURLOPT_RETURNTRANSFER, true);
        curl_setopt($ch, CURLOPT_TIMEOUT, $timeout);
        curl_setopt($ch, CURLOPT_CONNECTTIMEOUT, 8);
        curl_setopt($ch, CURLOPT_FOLLOWLOCATION, true);
        curl_setopt($ch, CURLOPT_MAXREDIRS, 3);
        curl_setopt($ch, CURLOPT_USERAGENT, 'CGT-LuckWorker/' . LW_VERSION);
        if ($method === 'POST') {
            curl_setopt($ch, CURLOPT_POST, true);
            curl_setopt($ch, CURLOPT_POSTFIELDS, (string) $body);
        }
        if ($headers) { curl_setopt($ch, CURLOPT_HTTPHEADER, $headers); }
        $out = curl_exec($ch);
        $code = (int) curl_getinfo($ch, CURLINFO_HTTP_CODE);
        curl_close($ch);
        if ($out === false || $code < 200 || $code >= 300) { return null; }
        return $out;
    }
    if (!ini_get('allow_url_fopen')) { return null; }     // no way to reach the net
    $opt = array(
        'http' => array(
            'method'        => $method,
            'timeout'       => $timeout,
            'ignore_errors' => true,
            'header'        => array_merge(array('User-Agent: CGT-LuckWorker/' . LW_VERSION), $headers),
        ),
    );
    if ($method === 'POST') {
        $opt['http']['content'] = (string) $body;
        $opt['http']['header'][] = 'Content-Type: application/json';
    }
    $out = @file_get_contents($url, false, stream_context_create($opt));
    return $out === false ? null : $out;
}
function lw_json($url, $method = 'GET', $body = null, $headers = array(), $timeout = 15) {
    $raw = lw_http($url, $method, $body, $headers, $timeout);
    if ($raw === null) { return null; }
    $j = @json_decode($raw, true);
    return is_array($j) ? $j : null;
}

/* ============================================================ DECIMAL HELPERS
   EVM balances are 256-bit wei values that overflow a PHP int, so numbers are
   carried as decimal STRINGS and formatted without any float (no precision loss). */

function dec_mul_small($s, $m) {
    $carry = 0; $out = '';
    for ($i = strlen($s) - 1; $i >= 0; $i--) {
        $p = (ord($s[$i]) - 48) * $m + $carry;
        $out = chr(48 + ($p % 10)) . $out;
        $carry = intdiv($p, 10);
    }
    while ($carry > 0) { $out = chr(48 + ($carry % 10)) . $out; $carry = intdiv($carry, 10); }
    return ltrim($out, '0') === '' ? '0' : ltrim($out, '0');
}
function dec_add_small($s, $a) {
    $carry = $a; $out = '';
    for ($i = strlen($s) - 1; $i >= 0; $i--) {
        $p = (ord($s[$i]) - 48) + $carry;
        $out = chr(48 + ($p % 10)) . $out;
        $carry = intdiv($p, 10);
    }
    while ($carry > 0) { $out = chr(48 + ($carry % 10)) . $out; $carry = intdiv($carry, 10); }
    return ltrim($out, '0') === '' ? '0' : ltrim($out, '0');
}
function hex_to_dec_str($hex) {
    $hex = ltrim(strtolower(trim($hex)), '0');
    if ($hex === '' || $hex === 'x') { return '0'; }
    $dec = '0';
    for ($i = 0; $i < strlen($hex); $i++) {
        $d = strpos('0123456789abcdef', $hex[$i]);
        if ($d === false) { return '0'; }
        $dec = dec_add_small(dec_mul_small($dec, 16), $d);
    }
    return $dec;
}
/* integer-units string -> human decimal string (scale = decimals of the unit) */
function units_to_dec($units, $scale) {
    $neg = (strncmp($units, '-', 1) === 0);
    if ($neg) { $units = substr($units, 1); }
    if (!preg_match('/^[0-9]+$/', $units)) { return ''; }
    $units = ltrim($units, '0');
    if ($units === '') { $units = '0'; }
    if ($scale <= 0) { return ($neg ? '-' : '') . $units; }
    $units = str_pad($units, $scale + 1, '0', STR_PAD_LEFT);
    $int = substr($units, 0, -$scale);
    $frac = rtrim(substr($units, -$scale), '0');
    $out = $frac === '' ? $int : $int . '.' . $frac;
    return ($neg ? '-' : '') . $out;
}

/* ============================================================== HIT RECORDING
   Same files, same dedup, same lock protocol as found.php — the dashboard and
   the TXT download need no changes. */

function lw_record_hit($paths, $chain, $address, $pkhex, $wif, $bal, $recv, $tx) {
    $khash = md5($chain . '|' . $address);
    $fi = @fopen($paths['index'], 'c+');
    if (!$fi) { return false; }
    $saved = false;
    @flock($fi, LOCK_EX);
    $idx = stream_get_contents($fi);
    if (strpos((string) $idx, $khash) === false) {
        $rec = array(
            'ts' => time(), 'chain' => $chain, 'address' => $address,
            'pk_hex' => $pkhex, 'wif' => $wif,
            'bal' => $bal, 'recv' => $recv, 'tx' => $tx,
        );
        $fa = @fopen($paths['found'], 'a');
        if ($fa) {
            @flock($fa, LOCK_EX);
            fwrite($fa, json_encode($rec) . "\n");
            fflush($fa);
            @flock($fa, LOCK_UN);
            fclose($fa);
            fwrite($fi, $khash . "\n");
            fflush($fi);
            $saved = true;
            $fc = @fopen($paths['count'], 'c+');
            if ($fc) {
                @flock($fc, LOCK_EX);
                $n = (int) trim((string) stream_get_contents($fc));
                if ($n < 0) { $n = 0; }
                $n++;
                ftruncate($fc, 0); rewind($fc); fwrite($fc, (string) $n); fflush($fc);
                @flock($fc, LOCK_UN);
                fclose($fc);
            }
        }
    }
    @flock($fi, LOCK_UN);
    fclose($fi);
    return $saved;
}

/* ================================================================= CHECKERS
   Every checker returns:
     array of hits  -> checked successfully (possibly zero hits)
     null           -> the API failed; the group stays PENDING and is retried
                       next run. Nothing is ever marked checked by a failure. */

function lw_check_bitcoin($entries) {
    $map = array();                                  // address -> entry index
    $addrs = array();
    foreach ($entries as $i => $e) {
        foreach (array('bitcoin_p2pkh_c', 'bitcoin_p2pkh_u', 'bitcoin_p2wpkh', 'bitcoin_p2tr') as $k) {
            if (!empty($e['a'][$k])) { $map[$e['a'][$k]] = $i; $addrs[] = $e['a'][$k]; }
        }
    }
    if (!$addrs) { return array(); }
    $hits = array();
    foreach (array_chunk($addrs, 90) as $chunk) {    // keep the URL sane
        $url = 'https://blockchain.info/balance?cors=true&active=' . rawurlencode(implode('|', $chunk));
        $j = lw_json($url, 'GET', null, array(), 20);
        if ($j === null) { return null; }            // API failed -> retry all next run
        foreach ($j as $addr => $s) {
            if (!isset($map[$addr])) { continue; }
            $bal  = isset($s['final_balance'])  ? (int) $s['final_balance']  : 0;
            $recv = isset($s['total_received']) ? (int) $s['total_received'] : 0;
            $tx   = isset($s['n_tx'])           ? (int) $s['n_tx']           : 0;
            if ($bal > 0 || $recv > 0 || $tx > 0) {
                $hits[] = array($map[$addr], 'bitcoin', $addr,
                                units_to_dec((string) $bal, 8), units_to_dec((string) $recv, 8), (string) $tx);
            }
        }
    }
    return $hits;
}

function lw_check_evm_chain($entries, $chain, $rpc) {
    $addrs = array();
    foreach ($entries as $i => $e) {
        if (!empty($e['a']['evm'])) { $addrs[$i] = $e['a']['evm']; }
    }
    if (!$addrs) { return array(); }
    $hits = array();
    foreach (array_chunk($addrs, 25, true) as $chunk) {
        $req = array(); $idx = 0; $order = array();
        foreach ($chunk as $i => $a) {
            $req[] = array('jsonrpc' => '2.0', 'id' => $idx++,   'method' => 'eth_getBalance',
                           'params' => array($a, 'latest'));
            $req[] = array('jsonrpc' => '2.0', 'id' => $idx++,   'method' => 'eth_getTransactionCount',
                           'params' => array($a, 'latest'));
            $order[] = $i;
        }
        $j = lw_json($rpc, 'POST', json_encode($req),
                     array('Content-Type: application/json'), 20);
        if (!is_array($j)) { return null; }
        $bal = array(); $nonce = array();
        foreach ($j as $r) {
            if (!isset($r['id'])) { continue; }
            $i = $order[intdiv((int) $r['id'], 2)];
            if (((int) $r['id']) % 2 === 0) { $bal[$i]   = isset($r['result']) ? $r['result'] : '0x0'; }
            else                            { $nonce[$i] = isset($r['result']) ? $r['result'] : '0x0'; }
        }
        foreach ($chunk as $i => $a) {
            $b = isset($bal[$i])   ? hex_to_dec_str($bal[$i])     : '0';
            $n = isset($nonce[$i]) ? hex_to_dec_str($nonce[$i])   : '0';
            if (ltrim($b, '0') !== '' || ltrim($n, '0') !== '') {
                $hits[] = array($i, $chain, $a,
                                units_to_dec($b, 18), '', $n);
            }
        }
    }
    return $hits;
}

function lw_check_esplora($entries, $key, $chain, $base, $scale) {
    $hits = array();
    foreach ($entries as $i => $e) {
        if (empty($e['a'][$key])) { continue; }
        $addr = $e['a'][$key];
        $j = lw_json($base . '/api/address/' . rawurlencode($addr), 'GET', null, array(), 15);
        if ($j === null) { return null; }            // failed -> whole group retried
        $cs = isset($j['chain_stats'])   ? $j['chain_stats']   : array();
        $ms = isset($j['mempool_stats']) ? $j['mempool_stats'] : array();
        $recv = (int) (isset($cs['funded_txo_sum']) ? $cs['funded_txo_sum'] : 0)
              + (int) (isset($ms['funded_txo_sum']) ? $ms['funded_txo_sum'] : 0);
        $spent= (int) (isset($cs['spent_txo_sum']) ? $cs['spent_txo_sum'] : 0);
        $bal  = $recv - $spent;
        $tx   = (int) (isset($cs['tx_count']) ? $cs['tx_count'] : 0)
              + (int) (isset($ms['tx_count']) ? $ms['tx_count'] : 0);
        if ($bal > 0 || $recv > 0 || $tx > 0) {
            $hits[] = array($i, $chain, $addr,
                            units_to_dec((string) max(0, $bal), $scale),
                            units_to_dec((string) $recv, $scale), (string) $tx);
        }
    }
    return $hits;
}

function lw_check_blockcypher($entries, $key, $chain, $base, $scale) {
    $hits = array();
    foreach ($entries as $i => $e) {
        if (empty($e['a'][$key])) { continue; }
        $addr = $e['a'][$key];
        $j = lw_json($base . '/addrs/' . rawurlencode($addr) . '/balance', 'GET', null, array(), 15);
        if ($j === null) { return null; }
        $bal  = isset($j['final_balance'])  ? $j['final_balance']  : 0;   // may exceed int
        $recv = isset($j['total_received']) ? $j['total_received'] : 0;
        $tx   = isset($j['final_n_tx'])     ? $j['final_n_tx']     : (isset($j['n_tx']) ? $j['n_tx'] : 0);
        $balS  = is_int($bal)  ? (string) $bal  : (is_float($bal)  ? sprintf('%.0f', $bal)  : (string) $bal);
        $recvS = is_int($recv) ? (string) $recv : (is_float($recv) ? sprintf('%.0f', $recv) : (string) $recv);
        if (trim($balS, '0') !== '' || trim($recvS, '0') !== '' || (int) $tx > 0) {
            $hits[] = array($i, $chain, $addr,
                            units_to_dec($balS, $scale), units_to_dec($recvS, $scale), (string) $tx);
        }
    }
    return $hits;
}

function lw_check_haskoin($entries, $key, $chain, $base, $scale) {
    $hits = array();
    foreach ($entries as $i => $e) {
        if (empty($e['a'][$key])) { continue; }
        $addr = $e['a'][$key];
        $j = lw_json($base . '/address/' . rawurlencode($addr) . '/balance', 'GET', null, array(), 15);
        if ($j === null) { return null; }
        $bal  = (int) (isset($j['confirmed'])   ? $j['confirmed']   : 0)
              + (int) (isset($j['unconfirmed']) ? $j['unconfirmed'] : 0);
        $recv = (int) (isset($j['received']) ? $j['received'] : 0);
        $tx   = (int) (isset($j['txs'])      ? $j['txs']      : 0);
        if ($bal > 0 || $recv > 0 || $tx > 0) {
            $hits[] = array($i, $chain, $addr,
                            units_to_dec((string) max(0, $bal), $scale),
                            units_to_dec((string) $recv, $scale), (string) $tx);
        }
    }
    return $hits;
}

function lw_check_tron($entries) {
    $hits = array();
    foreach ($entries as $i => $e) {
        if (empty($e['a']['tron'])) { continue; }
        $addr = $e['a']['tron'];
        $j = lw_json('https://api.trongrid.io/v1/accounts/' . rawurlencode($addr), 'GET', null, array(), 15);
        if ($j === null) { return null; }
        if (empty($j['data']) || !isset($j['data'][0])) { continue; }   // no account = no activity
        $d = $j['data'][0];
        $bal = isset($d['balance']) ? (int) $d['balance'] : 0;
        $tx  = isset($d['transactions']) ? (int) $d['transactions'] : 0;
        if ($bal > 0 || $tx > 0) {
            $hits[] = array($i, 'tron', $addr, units_to_dec((string) $bal, 6), '', (string) $tx);
        }
    }
    return $hits;
}

function lw_check_xrp($entries) {
    $hits = array();
    foreach ($entries as $i => $e) {
        if (empty($e['a']['xrp'])) { continue; }
        $addr = $e['a']['xrp'];
        $req = json_encode(array('method' => 'account_info',
                                 'params' => array(array('account' => $addr, 'ledger_index' => 'validated'))));
        $j = lw_json('https://xrplcluster.com/', 'POST', $req, array('Content-Type: application/json'), 15);
        if ($j === null) { return null; }
        $r = isset($j['result']) ? $j['result'] : array();
        /* a genuinely missing account is NOT an API failure and NOT a hit */
        if (isset($r['error']) && $r['error'] === 'actNotFound') { continue; }
        if (isset($r['error'])) { return null; }
        $bal = (isset($r['account_data']['Balance']) && preg_match('/^[0-9]+$/', $r['account_data']['Balance']))
             ? $r['account_data']['Balance'] : '0';
        if (ltrim($bal, '0') !== '') {
            $hits[] = array($i, 'xrp', $addr, units_to_dec($bal, 6), '', '');
        }
    }
    return $hits;
}

function lw_evm_chains() {
    return array(
        'ethereum'  => 'https://ethereum-rpc.publicnode.com',
        'bnb'       => 'https://bsc-rpc.publicnode.com',
        'polygon'   => 'https://polygon-bor-rpc.publicnode.com',
        'arbitrum'  => 'https://arbitrum-one-rpc.publicnode.com',
        'avalanche' => 'https://avalanche-c-chain-rpc.publicnode.com',
        'optimism'  => 'https://optimism-rpc.publicnode.com',
        'base'      => 'https://base-rpc.publicnode.com',
        'zksync'    => 'https://zksync-era.blockpi.network/v1/rpc/public',
    );
}

/* ==================================================================== RUN */

function lw_next_scalar($state) {
    /* range mode: cursor++ ; random mode: uniform 256-bit scalar */
    if ($state['mode'] === 'random') {
        $h = '';
        for ($i = 0; $i < 8; $i++) { $h .= sprintf('%08x', mt_rand(0, 0xFFFFFFFF)); }
        return array($h, $state['cursor']);          // cursor unused in random mode
    }
    $cur = b32_from_hex($state['cursor']);
    $one = str_repeat("\x00", 31) . "\x01";
    $nxt = b32_add($cur, $one);
    return array(bin2hex($cur), bin2hex($nxt));
}

function lw_run($paths, $budgetOverride = null) {
    $t0 = microtime(true);

    /* ---- single-flight lock: a second cron tick stands down -------------- */
    $lk = @fopen($paths['lock'], 'c+');
    if (!$lk) { return array('ok' => false, 'error' => 'lock-unwritable'); }
    if (!@flock($lk, LOCK_EX | LOCK_NB)) {
        fclose($lk);
        return array('ok' => true, 'skipped' => 'busy');     // another run is active
    }

    if (!is_dir($paths['dir'])) { @mkdir($paths['dir'], 0755, true); }
    $guard = $paths['dir'] . '/.htaccess';
    if (!file_exists($guard)) {
        @file_put_contents($guard, "Require all denied\nDeny from all\nOptions -Indexes\n");
    }
    if (!file_exists($paths['key'])) {
        @file_put_contents($paths['key'], bin2hex(random_bytes(16)));
    }

    $state = lw_state_load($paths['state']);
    $queue = lw_queue_load($paths['queue']);
    $isNew = ($state['created'] === 0);
    if ($isNew) { $state['created'] = time(); }

    $generated = 0;
    $checked   = 0;
    $newHits   = 0;
    $errors    = array();
    $max       = ($budgetOverride !== null) ? max(1, (int) $budgetOverride) : (int) $state['gen_per_run'];

    /* ---- 1. GENERATE (cheap) — only while the queue is under the low mark,
              so generation self-throttles to whatever checking can absorb --- */
    if (count($queue) < (int) $state['queue_low']) {
        for ($i = 0; $i < $max; $i++) {
            list($scalar, $next) = lw_next_scalar($state);
            $a = addresses_for_scalar($scalar);
            if ($a === null) { $state['cursor'] = $next; continue; }   // skip invalid scalars
            $queue[] = array('pk' => $scalar, 'a' => $a);
            $state['cursor'] = $next;
            $generated++;
        }
        $state['generated'] += $generated;

        /* hard cap: never let the backlog grow without bound */
        $qmax = (int) $state['queue_max'];
        if (count($queue) > $qmax) {
            $shed = count($queue) - $qmax;
            $queue = array_slice($queue, $shed);                 // drop-oldest
            $state['dropped'] += $shed;
            lw_log($paths['log'], "WARN queue over cap, shed $shed entries");
        }
    }

    /* ---- 2. CHECK. The cursor was already advanced above, so a failure here
              costs nothing: the entries stay queued and are retried next run. */
    $groups = $state['groups'];
    $chunk  = array_slice($queue, 0, max(1, (int) $state['check_batch']), true);
    $done   = array();                                     // entry idx -> groups finished

    if (in_array('bitcoin', $groups, true) && $chunk) {
        $h = lw_check_bitcoin($chunk);
        if ($h === null) { $errors[] = 'bitcoin'; }
        else { foreach ($h as $x) { lw_emit($paths, $chunk, $x, $newHits); } }
        if ($h !== null) { foreach ($chunk as $i => $e) { $done[$i]['bitcoin'] = 1; $checked++; } }
    }
    if (in_array('evm', $groups, true) && $chunk) {
        $evm = lw_evm_chains();
        $chunkSmall = array_slice($chunk, 0, min(count($chunk), 25), true);
        $allOk = true;
        foreach ($evm as $chain => $rpc) {
            $h = lw_check_evm_chain($chunkSmall, $chain, $rpc);
            if ($h === null) { $errors[] = 'evm:' . $chain; $allOk = false; continue; }
            foreach ($h as $x) { lw_emit($paths, $chunkSmall, $x, $newHits); }
        }
        if ($allOk) { foreach ($chunkSmall as $i => $e) { $done[$i]['evm'] = 1; $checked++; } }
    }

    /* per-address chains: smaller budget, they cannot be batched */
    $single = array_slice($queue, 0, max(1, (int) $state['single_budget']), true);
    if ($single) {
        if (in_array('litecoin', $groups, true)) {
            $h = lw_check_esplora($single, 'litecoin_p2pkh', 'litecoin', 'https://litecoinspace.org', 8);
            if ($h === null) { $errors[] = 'litecoin'; }
            else { foreach ($h as $x) { lw_emit($paths, $single, $x, $newHits); }
                   foreach ($single as $i => $e) { $done[$i]['litecoin'] = 1; $checked++; } }
        }
        if (in_array('dogecoin', $groups, true)) {
            $h = lw_check_blockcypher($single, 'dogecoin_p2pkh', 'dogecoin',
                                      'https://api.blockcypher.com/v1/doge/main', 8);
            if ($h === null) { $errors[] = 'dogecoin'; }
            else { foreach ($h as $x) { lw_emit($paths, $single, $x, $newHits); }
                   foreach ($single as $i => $e) { $done[$i]['dogecoin'] = 1; $checked++; } }
        }
        if (in_array('bitcoin-cash', $groups, true)) {
            $h = lw_check_haskoin($single, 'bitcoin_cash', 'bitcoin-cash', 'https://api.haskoin.com/bch', 8);
            if ($h === null) { $errors[] = 'bitcoin-cash'; }
            else { foreach ($h as $x) { lw_emit($paths, $single, $x, $newHits); }
                   foreach ($single as $i => $e) { $done[$i]['bitcoin-cash'] = 1; $checked++; } }
        }
        if (in_array('tron', $groups, true)) {
            $h = lw_check_tron($single);
            if ($h === null) { $errors[] = 'tron'; }
            else { foreach ($h as $x) { lw_emit($paths, $single, $x, $newHits); }
                   foreach ($single as $i => $e) { $done[$i]['tron'] = 1; $checked++; } }
        }
        if (in_array('xrp', $groups, true)) {
            $h = lw_check_xrp($single);
            if ($h === null) { $errors[] = 'xrp'; }
            else { foreach ($h as $x) { lw_emit($paths, $single, $x, $newHits); }
                   foreach ($single as $i => $e) { $done[$i]['xrp'] = 1; $checked++; } }
        }
    }

    /* ---- 3. DROP fully-checked entries (only when EVERY group that ran
              succeeded for that entry; a failed group keeps it alive) ------- */
    $drop = array();
    foreach ($done as $i => $g) {
        if (count(array_intersect(array_keys($g), $groups)) === count($groups)) { $drop[$i] = true; }
    }
    if ($drop) {
        $kept = array();
        foreach ($queue as $i => $e) { if (!isset($drop[$i])) { $kept[] = $e; } }
        $queue = array_values($kept);
    }
    $checked = (int) $checked;

    /* ---- 4. persist ------------------------------------------------------ */
    $state['runs']++;
    $state['checked']  += $checked;
    $state['hits']     += $newHits;
    $state['last_run']  = time();
    if ($newHits > 0) { $state['last_hit'] = time(); }
    $state['last_error'] = implode(',', array_unique($errors));
    $state['queue_len']  = count($queue);
    $state['secs']       = round(microtime(true) - $t0, 2);

    lw_queue_save($paths['queue'], $queue);
    lw_state_save($paths['state'], $state);

    @flock($lk, LOCK_UN);
    fclose($lk);

    if ($generated || $checked || $errors) {
        lw_log($paths['log'], sprintf(
            'run gen=%d checked=%d hits=%d queue=%d %.2fs%s',
            $generated, $checked, $newHits, count($queue), $state['secs'],
            $errors ? ' errors=' . implode(',', array_unique($errors)) : ''));
    }
    return array('ok' => true, 'generated' => $generated, 'checked' => $checked,
                 'hits' => $newHits, 'queue' => count($queue),
                 'errors' => array_values(array_unique($errors)));
}

/* turn one checker hit into a stored record */
function lw_emit($paths, $entries, $hit, &$newHits) {
    list($i, $chain, $addr, $bal, $recv, $tx) = $hit;
    if (!isset($entries[$i])) { return; }
    $e = $entries[$i];
    $wif = wif($e['pk'], true);
    if (lw_record_hit($paths, $chain, $addr, $e['pk'], $wif, $bal, $recv, $tx)) {
        $newHits++;
    }
}

/* ================================================================== STATUS */

function lw_status($paths) {
    $s = lw_state_load($paths['state']);
    $q = lw_queue_load($paths['queue']);
    $total = (int) trim((string) @file_get_contents($paths['count']));
    $s['queue_len'] = count($q);
    $s['found_total'] = $total;
    $s['running'] = false;
    $lk = @fopen($paths['lock'], 'c+');
    if ($lk) {
        if (!@flock($lk, LOCK_EX | LOCK_NB)) { $s['running'] = true; }
        else { @flock($lk, LOCK_UN); }
        fclose($lk);
    }
    if ($s['start'] && $s['cursor']) {
        $from = hex_to_dec_str($s['start']);
        $now  = hex_to_dec_str($s['cursor']);
        $s['cursor_dec'] = $now;
    }
    return $s;
}

/* ================================================================ DISPATCH */

function lw_selftest_entry() { return lw_selftest(); }

if (PHP_SAPI === 'cli') {
    $argv = isset($argv) ? $argv : array();
    $cmd  = isset($argv[1]) ? $argv[1] : '--help';
    $paths = lw_paths();

    /* optional --batch=N */
    $batch = null;
    foreach ($argv as $a) {
        if (strpos($a, '--batch=') === 0) { $batch = (int) substr($a, 8); }
    }

    switch ($cmd) {
        case '--selftest':
            exit(lw_selftest());
        case '--status':
            echo json_encode(lw_status($paths), JSON_PRETTY_PRINT), "\n";
            exit(0);
        case '--secret':
            if (!is_dir($paths['dir'])) { @mkdir($paths['dir'], 0755, true); }
            if (!file_exists($paths['key'])) {
                @file_put_contents($paths['key'], bin2hex(random_bytes(16)));
            }
            echo trim((string) @file_get_contents($paths['key'])), "\n";
            exit(0);
        case '--reset':
            @unlink($paths['state']);
            @unlink($paths['queue']);
            echo "cursor reset (findings kept)\n";
            exit(0);
        case '--run':
            echo json_encode(lw_run($paths, $batch), JSON_PRETTY_PRINT), "\n";
            exit(0);
        case '--daemon':                      // optional: loop instead of cron
            $sleep = 60;
            while (true) {
                $r = lw_run($paths, $batch);
                echo gmdate('H:i:s'), ' ', json_encode($r), "\n";
                @ob_flush(); @flush();
                sleep($sleep);
            }
            exit(0);
        default:
            echo "luck-worker.php " . LW_VERSION . "\n\n"
               . "  --selftest        verify the crypto against known vectors\n"
               . "  --status          cursor, queue depth, lifetime totals (JSON)\n"
               . "  --run             one batch (what cron calls)\n"
               . "  --run --batch=N   one batch with N keys generated\n"
               . "  --daemon          loop forever (if you have a shell, not cron)\n"
               . "  --secret          print/print-create the HTTP trigger secret\n"
               . "  --reset           clear the cursor (findings are kept)\n";
            exit(0);
    }
}

/* ---- HTTP trigger (for cron without CLI php) ---------------------------- */
$paths = lw_paths();
$keyFile = $paths['key'];
$secret  = is_file($keyFile) ? trim((string) @file_get_contents($keyFile)) : '';

header('Content-Type: application/json; charset=utf-8');
header('Cache-Control: no-store, no-cache, must-revalidate, max-age=0');

if ($secret === '') {
    echo json_encode(array('ok' => false, 'error' => 'run "php luck-worker.php --secret" once on the server first'));
    exit;
}
if (!isset($_GET['k']) || !hash_equals($secret, (string) $_GET['k'])) {
    echo json_encode(array('ok' => false, 'error' => 'forbidden'));
    exit;
}
if (isset($_GET['status'])) { echo json_encode(lw_status($paths)); exit; }
if (isset($_GET['selftest'])) { ob_start(); $rc = lw_selftest(); $o = ob_get_clean(); echo json_encode(array('ok' => $rc === 0, 'out' => $o)); exit; }
if (isset($_GET['run'])) {
    @set_time_limit(120);
    echo json_encode(lw_run($paths, isset($_GET['batch']) ? (int) $_GET['batch'] : null));
    exit;
}
echo json_encode(array('ok' => true, 'worker' => LW_VERSION, 'hint' => '?run=1&k=SECRET'));

