<?php
/* ============================================================================
   stats.php  —  per-domain visitor counter (same-origin JSON endpoint)

   Returns TWO real numbers, no labels, no invented data:
     live  = distinct visitors with the site open right now
             (clients that pinged within the last WINDOW seconds — real-time)
     total = cumulative unique visitors ever, persisted forever (never resets)

   Response:  {"ok":true,"live":<int>,"total":<int>}

   Storage (created at runtime on the host, one set per domain, so .com/.org/.in
   each count themselves independently):
     stats-data/live.json  — { clientId: lastSeenUnixTs, ... }   (pruned to WINDOW)
     stats-data/total.txt  — a single integer, incremented once per new browser

   Hardened the same way as coop-proxy.php: errors silenced, no-store, atomic
   file writes under an exclusive lock. No external calls. If storage is ever
   unwritable it degrades to {live:1,total:0} rather than fabricating numbers.
   ============================================================================ */

@ini_set('display_errors', '0');
error_reporting(0);

header('Content-Type: application/json; charset=utf-8');
header('Cache-Control: no-store, no-cache, must-revalidate, max-age=0');
header('Pragma: no-cache');
header('Access-Control-Allow-Origin: *');

$WINDOW = 90;                       // seconds a client stays "live" after its last ping (>= 2x poll interval)
$DIR    = __DIR__ . '/stats-data';  // per-domain data dir (lives beside this file)

$now = time();

/* --- ensure a private, non-listable data dir (first run only) ------------- */
if (!is_dir($DIR)) { @mkdir($DIR, 0755, true); }
$guard = $DIR . '/.htaccess';
if (is_dir($DIR) && !file_exists($guard)) {
    @file_put_contents($guard, "Require all denied\nDeny from all\nOptions -Indexes\n");
}

$liveFile  = $DIR . '/live.json';
$totalFile = $DIR . '/total.txt';

/* --- client id: ephemeral, supplied by the browser; strictly sanitised ---- */
$id = isset($_GET['id']) ? preg_replace('/[^A-Za-z0-9_-]/', '', (string) $_GET['id']) : '';
if (strlen($id) < 6) {   // no/short id -> derive a stable-ish fallback so we still count 1
    $id = 'x' . substr(md5(($_SERVER['REMOTE_ADDR'] ?? '') . '|' . ($_SERVER['HTTP_USER_AGENT'] ?? '')), 0, 20);
}
if (strlen($id) > 64) { $id = substr($id, 0, 64); }

/* ---------------------------------------------------------------------------
   LIVE — presence map { id => lastSeenTs }, stale entries pruned to WINDOW.
   $alreadyLive tells us whether this client was already present this window
   (used below as a cookieless backstop against inflating TOTAL).
--------------------------------------------------------------------------- */
$live = array();
$alreadyLive = false;
$fp = @fopen($liveFile, 'c+');
if ($fp) {
    @flock($fp, LOCK_EX);
    $raw = stream_get_contents($fp);
    if ($raw !== false && strlen($raw)) {
        $tmp = json_decode($raw, true);
        if (is_array($tmp)) { $live = $tmp; }
    }
    foreach ($live as $k => $ts) {                 // prune stale / malformed
        if (!ctype_digit((string) $ts) || ($now - (int) $ts) > $WINDOW) { unset($live[$k]); }
    }
    $alreadyLive = isset($live[$id]);
    $live[$id] = $now;                              // mark this client present now
    ftruncate($fp, 0);
    rewind($fp);
    fwrite($fp, json_encode($live));
    fflush($fp);
    @flock($fp, LOCK_UN);
    fclose($fp);
}
$liveCount = count($live);
if ($liveCount < 1) { $liveCount = 1; }             // the caller is here -> at least 1

/* ---------------------------------------------------------------------------
   TOTAL — cumulative unique visitors, +1 on first visit per browser.
   Primary gate: the long-lived cookie 'cgt_v' (a returning browser is never
   recounted). Backstop for cookie-blocked browsers: only count when this
   client wasn't already in the live window, bounding inflation to ~1 / WINDOW.
--------------------------------------------------------------------------- */
$total = 0;
$fpt = @fopen($totalFile, 'c+');
if ($fpt) {
    @flock($fpt, LOCK_EX);
    $raw   = stream_get_contents($fpt);
    $total = (int) trim((string) $raw);
    if ($total < 0) { $total = 0; }

    $isNew = (!isset($_COOKIE['cgt_v'])) && (!$alreadyLive);
    if ($isNew) {
        $total += 1;
        ftruncate($fpt, 0);
        rewind($fpt);
        fwrite($fpt, (string) $total);
        fflush($fpt);
    }
    @flock($fpt, LOCK_UN);
    fclose($fpt);

    if ($isNew && !headers_sent()) {                // 10-year cookie so returns aren't recounted
        @setcookie('cgt_v', '1', $now + 315360000, '/');
    }
}

echo json_encode(array('ok' => true, 'live' => $liveCount, 'total' => $total));
