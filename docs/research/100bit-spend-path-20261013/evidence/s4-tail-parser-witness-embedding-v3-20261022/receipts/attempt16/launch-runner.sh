#!/bin/bash
set -u
P=/tmp/s4-tail-parser-embedding-v1/attempt16
lock=/tmp/aspis-local-lean.lock.d
lean=/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean
src="$P/sources/S4TailRunTraceScalarEmbeddingV1.lean"
obj="$P/objects/S4TailRunTraceScalarEmbeddingV1.olean"
E="$P/evidence"
start=$(date -u +%Y-%m-%dT%H:%M:%SZ); waited=0
while ! mkdir "$lock" 2>/dev/null; do if [ "$waited" -ge 55 ]; then echo LOCK_BUSY; exit 75; fi; sleep 0.25; waited=$((waited+1)); done
inode=$(stat -f '%i' "$lock"); pid=$$
printf '{"pid":%s,"target":"S4TailRunTraceScalarEmbeddingV1-attempt16","inode":%s}\n' "$pid" "$inode" > "$lock/owner.json"
cleanup(){ if [ -d "$lock" ] && [ "$(stat -f '%i' "$lock" 2>/dev/null)" = "$inode" ] && [ -f "$lock/owner.json" ] && rg -q '"pid":'"$pid"'[,}]' "$lock/owner.json"; then rm -f "$lock/owner.json"; rmdir "$lock" 2>/dev/null || true; fi; }
trap cleanup EXIT INT TERM
LEAN_PATH="/tmp/s4-tail-parser-embedding-v1/attempt15/objects:/tmp/root-s4-tail-trace-member-witness-v1-20261022/objects:$(cat "$E/LEAN_PATH.txt")"; export LEAN_PATH
rev=$(git rev-parse HEAD)
printf '{"argv":["%s","-j1","-M","4400","-R","%s","-o","%s","%s"],"revision_at_launch":"%s","start_utc":"%s","lock_inode":%s,"lock_pid":%s}\n' "$lean" "$P/sources" "$obj" "$src" "$rev" "$start" "$inode" "$pid" > "$E/command.json"
shasum -a 256 "$src" > "$E/source-before.sha256"; shasum -a 256 "$lean" > "$E/compiler.sha256"
/usr/bin/time -l "$lean" -j1 -M 4400 -R "$P/sources" -o "$obj" "$src" > "$E/lean.log" 2> "$E/time.log"; status=$?
shasum -a 256 "$src" > "$E/source-after.sha256"; end=$(date -u +%Y-%m-%dT%H:%M:%SZ); printf '%s\n' "$status" > "$E/exit.txt"
RSS=$(awk '/maximum resident set size/ {print $1}' "$E/time.log"|tail -1); sec=$(awk '/real/ {print $1}' "$E/time.log"|head -1); sw=$(awk '/swaps/ {print $1}' "$E/time.log"|tail -1); oh=null; [ -f "$obj" ] && oh="\"$(shasum -a 256 "$obj"|awk '{print $1}')\""
printf '{"target":"S4TailRunTraceScalarEmbeddingV1-attempt16","exit_status":%s,"wall_seconds":"%s","peak_rss_bytes":%s,"swap":%s,"source_sha256_before":"%s","source_sha256_after":"%s","object_sha256":%s,"revision_at_launch":"%s","compiler_sha256":"%s","end_utc":"%s"}\n' "$status" "$sec" "${RSS:-null}" "${sw:-null}" "$(awk '{print $1}' "$E/source-before.sha256")" "$(awk '{print $1}' "$E/source-after.sha256")" "$oh" "$rev" "$(awk '{print $1}' "$E/compiler.sha256")" "$end" > "$E/receipt.json"
cat "$E/lean.log"; cat "$E/receipt.json"; exit "$status"
