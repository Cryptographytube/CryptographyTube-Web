<?php
/* ============================================================================
   community/api.php  —  per-domain anonymous discussion board (same-origin JSON)

   A tiny, dependency-free forum backend for the static site. No database, no
   external calls — just hardened flat-file storage, exactly like stats.php /
   found.php. One data set per domain, so .com / .org / .in each keep their own
   threads independently.

   Endpoints (all same-origin; the page at /community/ calls ./api.php):
     GET   ?action=list&offset=0&limit=20   -> {ok,total,items:[thread summaries]}  newest-active first
     GET   ?action=thread&id=<id>           -> {ok,thread:{..},replies:[..]}
     POST  action=new    {nick,title,body}  -> {ok,id}
     POST  action=reply  {id,nick,body}     -> {ok,rid}

   Storage (created at runtime, private + non-listable):
     community-data/threads.json      — { id => {id,nick,title,body,ts,replies,last_ts} }
     community-data/reply/<id>.jsonl  — one reply record per line (append-only)
     community-data/rate.json         — { ipHash => lastPostTs }  (flood gate, pruned)
     community-data/.htaccess         — deny-guard (same as stats-data/found-data)

   Hardening (mirrors stats.php): errors silenced, no-store, atomic writes under
   an exclusive lock, no external calls, strict input sanitising + length caps,
   a honeypot field and a per-IP cooldown against spam. User text is stored
   sanitised and MUST be rendered client-side with textContent (never innerHTML),
   which community.js does — so stored markup can never execute.
   ============================================================================ */

@ini_set('display_errors', '0');
error_reporting(0);

header('Content-Type: application/json; charset=utf-8');
header('Cache-Control: no-store, no-cache, must-revalidate, max-age=0');
header('Pragma: no-cache');
header('X-Content-Type-Options: nosniff');

/* ---- config --------------------------------------------------------------- */
$DIR        = __DIR__ . '/community-data';   // per-domain data dir (beside this file)
$MAX_NICK   = 32;
$MAX_TITLE  = 120;
$MAX_BODY   = 4000;
$LIST_CAP   = 50;        // hard cap on page size
$COOLDOWN   = 10;        // seconds a given IP must wait between posts
$HOUR_CAP   = 40;        // max posts per IP per rolling hour
$THREAD_CAP = 5000;      // keep at most this many threads (oldest trimmed)

$now = time();

/* ---- JSON reply helper ---------------------------------------------------- */
function out($arr) { echo json_encode($arr); exit; }
function fail($msg) { out(array('ok' => false, 'error' => (string) $msg)); }

/* ---- ensure a private, non-listable data dir (first run only) ------------- */
if (!is_dir($DIR)) { @mkdir($DIR, 0755, true); }
$guard = $DIR . '/.htaccess';
if (is_dir($DIR) && !file_exists($guard)) {
    @file_put_contents($guard, "Require all denied\nDeny from all\nOptions -Indexes\n");
}
if (!is_dir($DIR)) { fail('storage unavailable'); }

$THREADS = $DIR . '/threads.json';
$REPLY   = $DIR . '/reply';
$RATE    = $DIR . '/rate.json';

/* ---- small utilities ------------------------------------------------------ */

/* Strip control chars (keep \n and \t), normalise newlines, trim, hard-cap. */
function clean_text($s, $max, $allow_nl = false) {
    $s = (string) $s;
    $s = str_replace(array("\r\n", "\r"), "\n", $s);
    if (!$allow_nl) { $s = str_replace("\n", ' ', $s); }
    // remove control chars except \n (0x0A) and \t (0x09)
    $s = preg_replace('/[\x00-\x08\x0B\x0C\x0E-\x1F\x7F]/u', '', $s);
    if ($s === null) { $s = ''; }           // invalid UTF-8 -> drop
    if ($allow_nl) { $s = preg_replace("/\n{3,}/", "\n\n", $s); }  // collapse blank runs
    $s = trim($s);
    // length cap in characters (multibyte-aware when available)
    if (function_exists('mb_substr')) {
        if (mb_strlen($s, 'UTF-8') > $max) { $s = mb_substr($s, 0, $max, 'UTF-8'); }
    } else {
        if (strlen($s) > $max) { $s = substr($s, 0, $max); }
    }
    return $s;
}

function new_id() {
    // 8 bytes of time + randomness -> short, URL-safe, sortable-ish, collision-safe enough
    return substr(dechex(time()), -8) . bin2hex(function_exists('random_bytes') ? random_bytes(5) : pack('N', mt_rand()));
}

function ip_hash() {
    $ip = $_SERVER['REMOTE_ADDR'] ?? '';
    return substr(md5('cgt-community|' . $ip), 0, 16);
}

/* Read a JSON map file under a shared lock. Returns array (possibly empty). */
function read_json_map($file) {
    $data = array();
    $fp = @fopen($file, 'r');
    if ($fp) {
        @flock($fp, LOCK_SH);
        $raw = stream_get_contents($fp);
        @flock($fp, LOCK_UN);
        fclose($fp);
        if ($raw !== false && strlen($raw)) {
            $tmp = json_decode($raw, true);
            if (is_array($tmp)) { $data = $tmp; }
        }
    }
    return $data;
}

/* ---- POST flood gate (cooldown + hourly cap), atomic under lock ----------- */
function rate_ok($RATE, $now, $COOLDOWN, $HOUR_CAP) {
    $me = ip_hash();
    $ok = true;
    $fp = @fopen($RATE, 'c+');
    if (!$fp) { return true; }                 // storage issue -> don't block posting
    @flock($fp, LOCK_EX);
    $raw = stream_get_contents($fp);
    $map = array();
    if ($raw !== false && strlen($raw)) {
        $tmp = json_decode($raw, true);
        if (is_array($tmp)) { $map = $tmp; }
    }
    // prune anything older than 1h and malformed entries
    foreach ($map as $k => $v) {
        if (!is_array($v) || !isset($v['t']) || ($now - (int) $v['t']) > 3600) { unset($map[$k]); }
    }
    $rec = isset($map[$me]) && is_array($map[$me]) ? $map[$me] : array('t' => 0, 'n' => 0, 'h' => $now);
    if (($now - (int) $rec['t']) < $COOLDOWN) { $ok = false; }           // too soon
    if ((int) $rec['n'] >= $HOUR_CAP && ($now - (int) $rec['h']) <= 3600) { $ok = false; } // hourly cap
    if ($ok) {
        if (($now - (int) $rec['h']) > 3600) { $rec['h'] = $now; $rec['n'] = 0; } // new hour window
        $rec['t'] = $now;
        $rec['n'] = (int) $rec['n'] + 1;
        $map[$me] = $rec;
        ftruncate($fp, 0); rewind($fp);
        fwrite($fp, json_encode($map)); fflush($fp);
    }
    @flock($fp, LOCK_UN);
    fclose($fp);
    return $ok;
}

/* ========================================================================== */
$action = isset($_GET['action']) ? (string) $_GET['action'] : '';
$method = $_SERVER['REQUEST_METHOD'] ?? 'GET';

/* ---------- GET: list ------------------------------------------------------ */
if ($method === 'GET' && $action === 'list') {
    $offset = isset($_GET['offset']) ? max(0, (int) $_GET['offset']) : 0;
    $limit  = isset($_GET['limit'])  ? (int) $_GET['limit'] : 20;
    if ($limit < 1) { $limit = 20; }
    if ($limit > $LIST_CAP) { $limit = $LIST_CAP; }

    $threads = read_json_map($THREADS);
    // newest-active first (by last_ts, fall back to ts)
    usort($threads, function ($a, $b) {
        $la = isset($a['last_ts']) ? (int) $a['last_ts'] : (int) ($a['ts'] ?? 0);
        $lb = isset($b['last_ts']) ? (int) $b['last_ts'] : (int) ($b['ts'] ?? 0);
        return $lb - $la;
    });
    $total = count($threads);
    $slice = array_slice($threads, $offset, $limit);
    $items = array();
    foreach ($slice as $t) {
        $body = (string) ($t['body'] ?? '');
        $preview = function_exists('mb_substr') ? mb_substr($body, 0, 160, 'UTF-8') : substr($body, 0, 160);
        $items[] = array(
            'id'      => (string) ($t['id'] ?? ''),
            'nick'    => (string) ($t['nick'] ?? 'anon'),
            'title'   => (string) ($t['title'] ?? ''),
            'preview' => $preview,
            'ts'      => (int) ($t['ts'] ?? 0),
            'last_ts' => (int) ($t['last_ts'] ?? ($t['ts'] ?? 0)),
            'replies' => (int) ($t['replies'] ?? 0),
        );
    }
    out(array('ok' => true, 'total' => $total, 'offset' => $offset, 'limit' => $limit, 'items' => $items));
}

/* ---------- GET: thread ---------------------------------------------------- */
if ($method === 'GET' && $action === 'thread') {
    $id = isset($_GET['id']) ? preg_replace('/[^a-f0-9]/', '', (string) $_GET['id']) : '';
    if (strlen($id) < 6 || strlen($id) > 40) { fail('bad id'); }
    $threads = read_json_map($THREADS);
    if (!isset($threads[$id])) { fail('not found'); }
    $t = $threads[$id];

    $replies = array();
    $rf = $REPLY . '/' . $id . '.jsonl';
    if (is_file($rf)) {
        $fp = @fopen($rf, 'r');
        if ($fp) {
            @flock($fp, LOCK_SH);
            while (($line = fgets($fp)) !== false) {
                $r = json_decode(trim($line), true);
                if (is_array($r)) {
                    $replies[] = array(
                        'nick' => (string) ($r['nick'] ?? 'anon'),
                        'body' => (string) ($r['body'] ?? ''),
                        'ts'   => (int) ($r['ts'] ?? 0),
                    );
                }
            }
            @flock($fp, LOCK_UN);
            fclose($fp);
        }
    }
    out(array(
        'ok' => true,
        'thread' => array(
            'id'      => (string) ($t['id'] ?? $id),
            'nick'    => (string) ($t['nick'] ?? 'anon'),
            'title'   => (string) ($t['title'] ?? ''),
            'body'    => (string) ($t['body'] ?? ''),
            'ts'      => (int) ($t['ts'] ?? 0),
            'last_ts' => (int) ($t['last_ts'] ?? ($t['ts'] ?? 0)),
            'replies' => (int) ($t['replies'] ?? count($replies)),
        ),
        'replies' => $replies,
    ));
}

/* ---------- POST: new thread ---------------------------------------------- */
if ($method === 'POST' && $action === 'new') {
    if (trim((string) ($_POST['website'] ?? '')) !== '') { out(array('ok' => true, 'id' => '')); } // honeypot -> shadow-drop
    $nick  = clean_text($_POST['nick']  ?? '', $MAX_NICK);
    $title = clean_text($_POST['title'] ?? '', $MAX_TITLE);
    $body  = clean_text($_POST['body']  ?? '', $MAX_BODY, true);
    if ($nick === '')  { $nick = 'anon'; }
    if ($title === '') { fail('title required'); }
    if ($body === '')  { fail('message required'); }
    if (!rate_ok($RATE, $now, $COOLDOWN, $HOUR_CAP)) { fail('slow down — please wait a few seconds'); }

    $id = new_id();
    $fp = @fopen($THREADS, 'c+');
    if (!$fp) { fail('storage unavailable'); }
    @flock($fp, LOCK_EX);
    $raw = stream_get_contents($fp);
    $map = array();
    if ($raw !== false && strlen($raw)) { $tmp = json_decode($raw, true); if (is_array($tmp)) { $map = $tmp; } }
    while (isset($map[$id])) { $id = new_id(); }       // guarantee uniqueness
    $map[$id] = array(
        'id' => $id, 'nick' => $nick, 'title' => $title, 'body' => $body,
        'ts' => $now, 'last_ts' => $now, 'replies' => 0,
    );
    // trim oldest if over cap
    if (count($map) > $THREAD_CAP) {
        uasort($map, function ($a, $b) { return (int) ($a['ts'] ?? 0) - (int) ($b['ts'] ?? 0); });
        $map = array_slice($map, count($map) - $THREAD_CAP, null, true);
    }
    ftruncate($fp, 0); rewind($fp);
    fwrite($fp, json_encode($map)); fflush($fp);
    @flock($fp, LOCK_UN);
    fclose($fp);
    out(array('ok' => true, 'id' => $id));
}

/* ---------- POST: reply ---------------------------------------------------- */
if ($method === 'POST' && $action === 'reply') {
    if (trim((string) ($_POST['website'] ?? '')) !== '') { out(array('ok' => true, 'rid' => '')); } // honeypot
    $id   = isset($_POST['id']) ? preg_replace('/[^a-f0-9]/', '', (string) $_POST['id']) : '';
    $nick = clean_text($_POST['nick'] ?? '', $MAX_NICK);
    $body = clean_text($_POST['body'] ?? '', $MAX_BODY, true);
    if (strlen($id) < 6 || strlen($id) > 40) { fail('bad id'); }
    if ($nick === '') { $nick = 'anon'; }
    if ($body === '') { fail('message required'); }
    if (!rate_ok($RATE, $now, $COOLDOWN, $HOUR_CAP)) { fail('slow down — please wait a few seconds'); }

    // thread must exist; bump its replies + last_ts atomically
    $fp = @fopen($THREADS, 'c+');
    if (!$fp) { fail('storage unavailable'); }
    @flock($fp, LOCK_EX);
    $raw = stream_get_contents($fp);
    $map = array();
    if ($raw !== false && strlen($raw)) { $tmp = json_decode($raw, true); if (is_array($tmp)) { $map = $tmp; } }
    if (!isset($map[$id])) { @flock($fp, LOCK_UN); fclose($fp); fail('not found'); }

    // append reply (own append-only file, own lock)
    if (!is_dir($REPLY)) { @mkdir($REPLY, 0755, true); }
    $rid = new_id();
    $rf  = $REPLY . '/' . $id . '.jsonl';
    $rfp = @fopen($rf, 'a');
    if ($rfp) {
        @flock($rfp, LOCK_EX);
        fwrite($rfp, json_encode(array('rid' => $rid, 'nick' => $nick, 'body' => $body, 'ts' => $now)) . "\n");
        fflush($rfp);
        @flock($rfp, LOCK_UN);
        fclose($rfp);
    } else {
        @flock($fp, LOCK_UN); fclose($fp); fail('storage unavailable');
    }

    $map[$id]['replies'] = (int) ($map[$id]['replies'] ?? 0) + 1;
    $map[$id]['last_ts'] = $now;
    ftruncate($fp, 0); rewind($fp);
    fwrite($fp, json_encode($map)); fflush($fp);
    @flock($fp, LOCK_UN);
    fclose($fp);
    out(array('ok' => true, 'rid' => $rid));
}

/* ---------- unknown -------------------------------------------------------- */
fail('unknown action');
