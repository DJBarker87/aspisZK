#!/usr/bin/env bash
set -uo pipefail
BASE=/home/dombarker/project-offloads/aspis-r1-terminal-extraction-20261016/attempt-a
cd "$BASE/input"
export PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin
export RUSTUP_TOOLCHAIN=nightly-2026-06-01
export CARGO_BUILD_JOBS=1
export CARGO_NET_OFFLINE=false
O="$BASE/receipts/metadata-regenerate-a"
mkdir -p "$O"
cp -n Cargo.lock "$O/Cargo.lock.before"
sha256sum Cargo.lock > "$O/lock-before.sha256"
start=$(date -u +%Y-%m-%dT%H:%M:%SZ); t0=$(date +%s%N)
CG=$(cut -d: -f3 /proc/self/cgroup); CGROOT=/sys/fs/cgroup$CG
printf 'start=%s\ncgroup=%s\ncommand=cargo metadata --format-version 1 (online resolution; no compilation)\n' "$start" "$CGROOT" > "$O/metadata.txt"
/usr/bin/time -v timeout 300s cargo metadata --format-version 1 > "$O/metadata.json" 2> "$O/command.log"
rc=$?
t1=$(date +%s%N); end=$(date -u +%Y-%m-%dT%H:%M:%SZ)
python3 - "$t0" "$t1" "$O/metadata.txt" "$rc" "$end" <<'PY'
import sys
s,e,path,rc,end=sys.argv[1:]
with open(path,"a") as f: f.write(f"exit={rc}\nend={end}\nwall_seconds={(int(e)-int(s))/1e9:.3f}\n")
PY
sha256sum Cargo.lock > "$O/lock-after.sha256"
diff -u "$O/Cargo.lock.before" Cargo.lock > "$O/lock.diff" || true
[ -r "$CGROOT/memory.peak" ] && cat "$CGROOT/memory.peak" > "$O/memory.peak" || true
[ -r "$CGROOT/memory.swap.current" ] && cat "$CGROOT/memory.swap.current" > "$O/memory.swap.current" || true
[ -r "$CGROOT/memory.events" ] && cat "$CGROOT/memory.events" > "$O/memory.events" || true
exit "$rc"
