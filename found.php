<?php
/* ============================================================================
   found.php  —  per-domain global "Found Luck" store (same-origin JSON endpoint)

   The Luck Puzzle pages auto-scan random keys in each visitor's browser. When a
   browser thinks it found activity it POSTs the address + its private key here.

   REAL, ON-CHAIN data only — the browser's numbers are NEVER trusted. Before
   storing, found.php independently re-checks the address against that chain's own
   public API (see luck-verify.php) and saves ONLY if the chain itself reports
   balance > 0, received > 0, or tx > 0 — storing the chain's numbers, not the
   browser's. Anything not positively confirmed is dropped (fail-closed), so a
   fabricated balance can never reach the board. With random keys a real hit is
   ~1 in 2^160, so this list will almost certainly stay empty; that is correct.

   Endpoints (one data set per domain, so .com/.org/.in each keep their own):
     POST  {chain,address,pk_hex,wif,bal,recv,tx}  -> append (deduped) ; {ok,saved,total}
     GET                                            -> {ok,total,offset,limit,items[]} newest-first
     GET  ?count=1                                  -> {ok,total}
     GET  ?download=txt                             -> streams the whole list as text/plain

   Storage (created at runtime, private + non-listable):
     found-data/found.jsonl  — one JSON record per line (append-only)
     found-data/index.txt    — md5(chain|address) per line (dedup gate)
     found-data/count.txt    — a single integer (unique records)

   Hardened like stats.php / coop-proxy.php: errors silenced, no-store, atomic
   locked writes, no external calls.
   ============================================================================ */

@ini_set('display_errors', '0');
error_reporting(0);

@include_once __DIR__ . '/luck-verify.php';   // independent on-chain verification (POST gate)

header('Cache-Control: no-store, no-cache, must-revalidate, max-age=0');
header('Pragma: no-cache');

$DIR   = __DIR__ . '/found-data';
$FOUND = $DIR . '/found.jsonl';
$INDEX = $DIR . '/index.txt';
$COUNT = $DIR . '/count.txt';

/* --- ensure a private, non-listable data dir (first run only) ------------- */
if (!is_dir($DIR)) { @mkdir($DIR, 0755, true); }
$guard = $DIR . '/.htaccess';
if (is_dir($DIR) && !file_exists($guard)) {
    @file_put_contents($guard, "Require all denied\nDeny from all\nOptions -Indexes\n");
}

function found_total($COUNT) {
    $t = (int) trim((string) @file_get_contents($COUNT));
    return $t < 0 ? 0 : $t;
}
function jexit($arr) {
    header('Content-Type: application/json; charset=utf-8');
    echo json_encode($arr);
    exit;
}

$method = isset($_SERVER['REQUEST_METHOD']) ? $_SERVER['REQUEST_METHOD'] : 'GET';

/* =====================================================================  POST  */
if ($method === 'POST') {
    $raw = file_get_contents('php://input');
    $in  = json_decode((string) $raw, true);
    if (!is_array($in)) { $in = $_POST; }

    $chain   = isset($in['chain'])   ? substr(preg_replace('/[^a-z0-9\-]/i', '', (string) $in['chain']), 0, 24)   : '';
    $address = isset($in['address']) ? substr(preg_replace('/[^A-Za-z0-9]/', '',  (string) $in['address']), 0, 120) : '';
    $pkhex   = isset($in['pk_hex'])  ? strtolower(preg_replace('/[^0-9a-fA-F]/', '', (string) $in['pk_hex']))      : '';
    $wif     = isset($in['wif'])     ? substr(preg_replace('/[^A-Za-z0-9]/', '',  (string) $in['wif']), 0, 120)    : '';
    $bal     = isset($in['bal'])     ? substr(preg_replace('/[^0-9A-Za-z\.\s\-]/', '', (string) $in['bal']), 0, 48)  : '';
    $recv    = isset($in['recv'])    ? substr(preg_replace('/[^0-9A-Za-z\.\s\-]/', '', (string) $in['recv']), 0, 48) : '';
    $tx      = isset($in['tx'])      ? substr(preg_replace('/[^0-9A-Za-z\.\s\-]/', '', (string) $in['tx']), 0, 48)   : '';

    // Sanity gate: require a plausible address + a full 64-hex private key.
    if ($address === '' || strlen($pkhex) !== 64) {
        jexit(array('ok' => false, 'error' => 'invalid', 'total' => found_total($COUNT)));
    }

    // REAL, ON-CHAIN gate: the browser's bal/recv/tx are NOT trusted. Ask the
    // chain's own public API whether this address truly has activity, and store
    // only what the chain reports. Anything not positively confirmed active is
    // never saved (fail-closed) — a fabricated balance can never reach the board.
    if (!function_exists('luck_verify_activity')) {
        // verifier not deployed — refuse to store anything unverified.
        jexit(array('ok' => true, 'saved' => false, 'active' => false,
                    'reason' => 'verify-unavailable', 'total' => found_total($COUNT)));
    }
    $chk = luck_verify_activity($chain, $address);
    if (!is_array($chk) || !isset($chk['status']) || $chk['status'] !== 'active') {
        // 'inactive' (verified empty) or 'unverified' (API down / not checkable).
        // Answer ok so the browser stops re-POSTing this dead address; save nothing.
        jexit(array(
            'ok'     => true,
            'saved'  => false,
            'active' => false,
            'reason' => (is_array($chk) && isset($chk['status'])) ? $chk['status'] : 'unverified',
            'total'  => found_total($COUNT),
        ));
    }
    // Overwrite with the server-verified figures — never the browser's.
    $bal  = (string) $chk['bal'];
    $recv = (string) $chk['recv'];
    $tx   = (string) $chk['tx'];

    $khash  = md5($chain . '|' . $address);
    $saved  = false;

    $fi = @fopen($INDEX, 'c+');
    if ($fi) {
        @flock($fi, LOCK_EX);
        $idx = stream_get_contents($fi);
        $seen = ($idx !== false && strpos($idx, $khash) !== false);
        if (!$seen) {
            $rec = array(
                'ts' => time(), 'chain' => $chain, 'address' => $address,
                'pk_hex' => $pkhex, 'wif' => $wif,
                'bal' => $bal, 'recv' => $recv, 'tx' => $tx,
            );
            $fa = @fopen($FOUND, 'a');
            if ($fa) {
                @flock($fa, LOCK_EX);
                fwrite($fa, json_encode($rec) . "\n");
                fflush($fa);
                @flock($fa, LOCK_UN);
                fclose($fa);

                fwrite($fi, $khash . "\n");   // mark seen only after the record landed
                fflush($fi);
                $saved = true;

                $fc = @fopen($COUNT, 'c+');
                if ($fc) {
                    @flock($fc, LOCK_EX);
                    $t = (int) trim((string) stream_get_contents($fc));
                    if ($t < 0) { $t = 0; }
                    $t += 1;
                    ftruncate($fc, 0); rewind($fc); fwrite($fc, (string) $t); fflush($fc);
                    @flock($fc, LOCK_UN);
                    fclose($fc);
                }
            }
        }
        @flock($fi, LOCK_UN);
        fclose($fi);
    }

    jexit(array('ok' => true, 'saved' => $saved, 'duplicate' => !$saved, 'total' => found_total($COUNT)));
}

/* =============================================================  GET download  */
if (isset($_GET['download'])) {
    header('Content-Type: text/plain; charset=utf-8');
    header('Content-Disposition: attachment; filename="found-luck.txt"');
    $fp = @fopen($FOUND, 'r');
    if ($fp) {
        @flock($fp, LOCK_SH);
        $i = 0;
        while (($line = fgets($fp)) !== false) {            // streamed: huge-file safe
            $r = json_decode(trim($line), true);
            if (!is_array($r)) { continue; }
            $i++;
            echo '[' . $i . '] ' . (isset($r['chain']) ? $r['chain'] : '') . "\r\n";
            echo 'Address:     ' . (isset($r['address']) ? $r['address'] : '') . "\r\n";
            echo 'PrivateKey:  ' . (isset($r['pk_hex']) ? $r['pk_hex'] : '') . "\r\n";
            if (!empty($r['wif']))  { echo 'WIF:         ' . $r['wif'] . "\r\n"; }
            echo 'Balance:     ' . (isset($r['bal']) ? $r['bal'] : '') . "\r\n";
            if (!empty($r['recv'])) { echo 'Received:    ' . $r['recv'] . "\r\n"; }
            if (!empty($r['tx']))   { echo 'Tx:          ' . $r['tx'] . "\r\n"; }
            if (!empty($r['ts']))   { echo 'Time:        ' . gmdate('Y-m-d H:i:s', (int) $r['ts']) . " UTC\r\n"; }
            echo "\r\n";
        }
        @flock($fp, LOCK_UN);
        fclose($fp);
    }
    exit;
}

/* ================================================================  GET count  */
if (isset($_GET['count'])) {
    jexit(array('ok' => true, 'total' => found_total($COUNT)));
}

/* =============================================================  GET list page  */
$offset = isset($_GET['offset']) ? max(0, (int) $_GET['offset']) : 0;
$limit  = isset($_GET['limit'])  ? (int) $_GET['limit'] : 100;
if ($limit < 1)    { $limit = 1; }
if ($limit > 1000) { $limit = 1000; }

$lines = array();
$fp = @fopen($FOUND, 'r');
if ($fp) {
    @flock($fp, LOCK_SH);
    while (($line = fgets($fp)) !== false) {
        $line = trim($line);
        if ($line !== '') { $lines[] = $line; }
    }
    @flock($fp, LOCK_UN);
    fclose($fp);
}
$lines = array_reverse($lines);                              // newest first
$slice = array_slice($lines, $offset, $limit);
$items = array();
foreach ($slice as $line) {
    $r = json_decode($line, true);
    if (is_array($r)) { $items[] = $r; }
}
jexit(array('ok' => true, 'total' => count($lines), 'offset' => $offset, 'limit' => $limit, 'items' => $items));
