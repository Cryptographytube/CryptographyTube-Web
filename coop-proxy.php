<?php
/**
 * coop-proxy.php  —  REAL Community-Hunt data for the live site (folder-only)
 * ---------------------------------------------------------------------------
 * The Bitcoin-puzzle "Team / Community Hunt" panel needs the SAME live numbers
 * as privatekeyfinder.io/bitcoin-puzzle/<N>/random. A browser on our live domain
 * CANNOT read that feed directly — privatekeyfinder blocks our origin (HTTP 400
 * on the /ws handshake). A SERVER can, though: server-side origins are allowed.
 *
 * So this tiny PHP endpoint (same origin as the site — no CORS, no extra host,
 * just one file in the folder) performs privatekeyfinder's Engine.IO (socket.io
 * v4) POLLING handshake server-side and returns the REAL snapshot as JSON:
 *
 *   GET coop-proxy.php?puzzle=71  ->
 *   { "ok":true, "puzzle":71,
 *     "snapshot":{puzzle,coveredKeys,cellsDone,remaining,totalKeys,pct,teamSpeed,hunters},
 *     "speedTotal":{speed,clients}, "ts":..., "cached":false }
 *
 * privatekeyfinder's polling transport sits behind a load balancer with NO
 * sticky sessions, so a POST right after the GET handshake often lands on a
 * different node -> {"code":1,"message":"Session ID unknown"} (~2 of 3 tries).
 * We simply RETRY the whole short handshake with a fresh sid until one lands on a
 * single node and the puzzle:watch ACK (packet "430[...]") comes back. That ACK
 * already carries the full snapshot, so we never need to hold a long-lived
 * session or ping/pong — one clean pass per poll.
 *
 * A tiny file cache (TTL seconds) shares one upstream pull across all visitors on
 * the same puzzle and smooths transient failures. If the feed can't be reached
 * we return the most recent REAL value if it's still fresh enough, else
 * {"ok":false,...}. We NEVER invent numbers — the client shows nothing rather
 * than fake data.
 *
 * Deploy: drop this file at the site root (same folder as index.html). Requires
 * PHP with the cURL extension and outbound HTTPS allowed (standard on cPanel).
 */

// Never let a PHP notice/warning leak into the JSON body (would corrupt it and
// could surface as "fake"/garbage in the panel). Keep output strictly JSON.
@ini_set('display_errors', '0');
error_reporting(0);
@set_time_limit(25);

header('Content-Type: application/json; charset=utf-8');
header('Cache-Control: no-store, max-age=0');
header('Access-Control-Allow-Origin: *');   // harmless; page is same-origin anyway

// ---- config ---------------------------------------------------------------
$UPSTREAM   = 'https://privatekeyfinder.io';
$WS_PATH    = '/ws/';
$MAX_TRIES  = 12;      // handshake attempts (each ~5 fast requests; success ~1/3 per try)
$REQ_TO     = 4;       // seconds per HTTP request
$WALL_TO    = 12;      // seconds overall budget for a cold pull
$CACHE_TTL  = 3;       // seconds a fresh snapshot is reused as-is
$STALE_OK   = 30;      // seconds an old REAL snapshot may still be served on failure

$puzzle = isset($_GET['puzzle']) ? (int)$_GET['puzzle'] : 0;
if ($puzzle < 1 || $puzzle > 160) { echo json_encode(array('ok'=>false,'error'=>'bad puzzle')); exit; }

if (!function_exists('curl_init')) { echo json_encode(array('ok'=>false,'error'=>'no curl')); exit; }

// op=snapshot (default) -> live community stats;  op=chunk -> a BATCH of real
// coop scan-ranges so the LIVE "Current chunk" bar can move with REAL work.
$op    = isset($_GET['op']) ? preg_replace('/[^a-z]/', '', $_GET['op']) : 'snapshot';
$BATCH = isset($_GET['n'])  ? max(1, min(16, (int)$_GET['n'])) : 8;

$cacheFile = rtrim(sys_get_temp_dir(), '/\\') . '/cgt_coop_' . $puzzle . '.json';
$now = time();

// ---- op=chunk : relay a BATCH of REAL coop scan-ranges ---------------------
// The engine's "Current chunk" bar advances by scanning a server-assigned range
// (chunk:req -> {start,end,...}). On the live site the browser can't reach the
// feed, so we claim a batch of REAL ranges server-side (one handshake, many
// chunk:req) and hand them to the client. Real work, real ranges — never faked.
// Not cached: every range must be unique.
if ($op === 'chunk') {
  $chunks = array();
  $st = microtime(true);
  for ($try = 0; $try < $MAX_TRIES; $try++) {
    if ((microtime(true) - $st) > $WALL_TO) break;
    $chunks = pull_chunks($UPSTREAM, $WS_PATH, $puzzle, $BATCH, $REQ_TO);
    if (count($chunks) > 0) break;
  }
  if (count($chunks) > 0) {
    echo json_encode(array('ok'=>true, 'puzzle'=>$puzzle, 'chunks'=>$chunks, 'ts'=>$now));
  } else {
    echo json_encode(array('ok'=>false, 'puzzle'=>$puzzle, 'error'=>'no chunks', 'ts'=>$now));
  }
  exit;
}

// ---- serve a FRESH cached snapshot without touching upstream ---------------
$cached = @file_get_contents($cacheFile);
if ($cached !== false) {
  $c = json_decode($cached, true);
  if (is_array($c) && isset($c['ts']) && ($now - $c['ts']) <= $CACHE_TTL && !empty($c['snapshot'])) {
    $c['ok'] = true; $c['cached'] = true;
    echo json_encode($c); exit;
  }
}

// ---------------------------------------------------------------------------
// low-level Engine.IO polling helpers
// ---------------------------------------------------------------------------
function eio_req($url, $post, $cookieJar, $to) {
  $ch = curl_init($url);
  $h  = array('Origin: https://privatekeyfinder.io', 'Accept: */*');
  curl_setopt_array($ch, array(
    CURLOPT_RETURNTRANSFER => true,
    CURLOPT_TIMEOUT        => $to,
    CURLOPT_CONNECTTIMEOUT => $to,
    CURLOPT_ENCODING       => '',
    CURLOPT_COOKIEFILE     => $cookieJar,
    CURLOPT_COOKIEJAR      => $cookieJar,
    CURLOPT_SSL_VERIFYPEER => true,
    CURLOPT_SSL_VERIFYHOST => 2,
    CURLOPT_FOLLOWLOCATION => false,
    CURLOPT_USERAGENT      => 'Mozilla/5.0 CGT-coop-proxy',
  ));
  if ($post !== null) {
    $h[] = 'Content-Type: text/plain;charset=UTF-8';
    curl_setopt($ch, CURLOPT_POST, true);
    curl_setopt($ch, CURLOPT_POSTFIELDS, $post);
  }
  curl_setopt($ch, CURLOPT_HTTPHEADER, $h);
  $body = curl_exec($ch);
  $code = curl_getinfo($ch, CURLINFO_HTTP_CODE);
  curl_close($ch);
  return array($code, $body === false ? '' : $body);
}

// Split an Engine.IO polling body into packets (record separator = 0x1e).
function eio_packets($body) { return explode("\x1e", $body); }

// Pull {snapshot, speedTotal} for one puzzle via one fresh handshake. Returns
// array(snapshot|null, speedTotal|null).
function pull_once($base, $wsPath, $puzzle, $reqTo) {
  $jar = tempnam(sys_get_temp_dir(), 'cgtck');
  $snapshot = null; $speedTotal = null;
  try {
    $q = $base . $wsPath . '?EIO=4&transport=polling';

    // 1) open handshake -> sid
    list($c1, $b1) = eio_req($q, null, $jar, $reqTo);
    if ($c1 !== 200 || $b1 === '') return array(null, null);
    $sid = null;
    foreach (eio_packets($b1) as $p) {
      if (strlen($p) && $p[0] === '0') {
        $j = json_decode(substr($p, 1), true);
        if (is_array($j) && isset($j['sid'])) { $sid = $j['sid']; break; }
      }
    }
    if ($sid === null) return array(null, null);
    $qs = $q . '&sid=' . rawurlencode($sid);

    // 2) connect default namespace
    list($c2, $b2) = eio_req($qs, '40', $jar, $reqTo);
    if ($c2 !== 200) return array(null, null);           // wrong node -> "Session ID unknown"

    // 3) read the namespace-connect ack (40{...}); ignore result contents
    eio_req($qs, null, $jar, $reqTo);

    // 4) subscribe to the puzzle (ack id 0 -> reply arrives as "430[...]")
    list($c4, $b4) = eio_req($qs, '420["puzzle:watch",{"puzzle":' . $puzzle . '}]', $jar, $reqTo);
    if ($c4 !== 200) return array(null, null);

    // 5) poll a few times for the 430 ack + a speed:total frame
    for ($i = 0; $i < 5 && $snapshot === null; $i++) {
      list($cg, $bg) = eio_req($qs, null, $jar, $reqTo);
      if ($cg !== 200) break;
      foreach (eio_packets($bg) as $p) {
        if ($p === '2') { eio_req($qs, '3', $jar, $reqTo); continue; }   // pong the ping
        if (strlen($p) >= 3 && substr($p, 0, 2) === '43') {              // ACK "43<id>[...]"
          $lb = strpos($p, '[');
          if ($lb !== false) {
            $arr = json_decode(substr($p, $lb), true);
            if (is_array($arr) && isset($arr[0]) && is_array($arr[0])) $snapshot = $arr[0];
          }
        } elseif (strlen($p) >= 2 && substr($p, 0, 2) === '42') {        // EVENT "42[name,payload]"
          $arr = json_decode(substr($p, 2), true);
          if (is_array($arr) && isset($arr[0])) {
            if ($arr[0] === 'puzzle:progress' && isset($arr[1]) && is_array($arr[1]) && (int)$arr[1]['puzzle'] === $puzzle) $snapshot = $arr[1];
            elseif ($arr[0] === 'speed:total' && isset($arr[1]) && is_array($arr[1])) $speedTotal = $arr[1];
          }
        }
      }
    }
  } catch (Exception $e) { /* fall through */ }
  @unlink($jar);
  return array($snapshot, $speedTotal);
}

// Claim a BATCH of REAL coop chunks via ONE fresh handshake: emit chunk:req $n
// times (ack ids 0..n-1) and collect the "43<id>[{...}]" acks. Each ack is a
// real server-assigned range {start,end,member,cells,coop}. Returns an array.
function pull_chunks($base, $wsPath, $puzzle, $n, $reqTo) {
  $jar = tempnam(sys_get_temp_dir(), 'cgtck');
  $out = array();
  try {
    $q = $base . $wsPath . '?EIO=4&transport=polling';

    list($c1, $b1) = eio_req($q, null, $jar, $reqTo);
    if ($c1 !== 200 || $b1 === '') { @unlink($jar); return $out; }
    $sid = null;
    foreach (eio_packets($b1) as $p) {
      if (strlen($p) && $p[0] === '0') {
        $j = json_decode(substr($p, 1), true);
        if (is_array($j) && isset($j['sid'])) { $sid = $j['sid']; break; }
      }
    }
    if ($sid === null) { @unlink($jar); return $out; }
    $qs = $q . '&sid=' . rawurlencode($sid);

    list($c2, $b2) = eio_req($qs, '40', $jar, $reqTo);
    if ($c2 !== 200) { @unlink($jar); return $out; }     // wrong node -> retry
    eio_req($qs, null, $jar, $reqTo);                     // read the 40 ack

    // fire chunk:req $n times back-to-back (ack ids 0..n-1)
    for ($k = 0; $k < $n; $k++) {
      eio_req($qs, '42' . $k . '["chunk:req",{"puzzle":' . $puzzle . ',"coop":true}]', $jar, $reqTo);
    }
    // drain the acks (server answers each "42<id>" with "43<id>[{...}]")
    for ($i = 0; $i < ($n + 4) && count($out) < $n; $i++) {
      list($cg, $bg) = eio_req($qs, null, $jar, $reqTo);
      if ($cg !== 200) break;
      foreach (eio_packets($bg) as $p) {
        if ($p === '2') { eio_req($qs, '3', $jar, $reqTo); continue; }   // pong
        if (strlen($p) >= 3 && substr($p, 0, 2) === '43') {             // ACK
          $lb = strpos($p, '[');
          if ($lb !== false) {
            $arr = json_decode(substr($p, $lb), true);
            if (is_array($arr) && isset($arr[0]) && is_array($arr[0]) && isset($arr[0]['start']) && isset($arr[0]['end'])) {
              $out[] = $arr[0];
            }
          }
        }
      }
    }
  } catch (Exception $e) { /* fall through */ }
  @unlink($jar);
  return $out;
}

// ---- retry the short handshake until the ACK lands (past the LB) -----------
$start = microtime(true);
$snapshot = null; $speedTotal = null;
for ($try = 0; $try < $MAX_TRIES; $try++) {
  if ((microtime(true) - $start) > $WALL_TO) break;
  list($s, $sp) = pull_once($UPSTREAM, $WS_PATH, $puzzle, $REQ_TO);
  if ($sp !== null && $speedTotal === null) $speedTotal = $sp;
  if ($s !== null && isset($s['puzzle']) && (int)$s['puzzle'] === $puzzle) { $snapshot = $s; break; }
}

// ---- respond --------------------------------------------------------------
if ($snapshot !== null) {
  $out = array(
    'ok'         => true,
    'puzzle'     => $puzzle,
    'snapshot'   => $snapshot,
    'speedTotal' => $speedTotal,   // may be null; client tolerates it
    'ts'         => $now,
    'cached'     => false,
  );
  @file_put_contents($cacheFile, json_encode($out), LOCK_EX);
  echo json_encode($out); exit;
}

// upstream failed this round: serve the most recent REAL snapshot if still fresh
if ($cached !== false) {
  $c = json_decode($cached, true);
  if (is_array($c) && isset($c['ts']) && ($now - $c['ts']) <= $STALE_OK && !empty($c['snapshot'])) {
    $c['ok'] = true; $c['cached'] = true; $c['stale'] = true;
    echo json_encode($c); exit;
  }
}

// nothing real to show — say so; the client shows NO fake data.
echo json_encode(array('ok'=>false, 'puzzle'=>$puzzle, 'error'=>'upstream unavailable', 'ts'=>$now));
