#!/usr/bin/env bash
set -uo pipefail
cd /home/dombarker/project-offloads/aspis-r1-terminal-extraction-20261016/attempt-a/input
export PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin RUSTUP_TOOLCHAIN=nightly-2026-06-01 CARGO_NET_OFFLINE=true
O=../receipts/metadata-original-lock-a
start=$(date -u +%Y-%m-%dT%H:%M:%SZ); t0=$(date +%s%N)
CG=$(cut -d: -f3 /proc/self/cgroup); CGROOT=/sys/fs/cgroup$CG
printf 'start=%s\ncgroup=%s\ncommand=cargo metadata --offline --locked --format-version 1\n' "$start" "$CGROOT" > "$O/metadata.txt"
/usr/bin/time -v timeout 300s cargo metadata --offline --locked --format-version 1 > "$O/metadata.json" 2> "$O/command.log"
rc=$?
t1=$(date +%s%N); end=$(date -u +%Y-%m-%dT%H:%M:%SZ)
python3 - "$t0" "$t1" "$O/metadata.txt" "$rc" "$end" <<'PY'
import sys
s,e,path,rc,end=sys.argv[1:]
with open(path,"a") as f: f.write(f"exit={rc}\nend={end}\nwall_seconds={(int(e)-int(s))/1e9:.3f}\n")
PY
[ -r "$CGROOT/memory.peak" ] && cat "$CGROOT/memory.peak" > "$O/memory.peak" || true
[ -r "$CGROOT/memory.swap.current" ] && cat "$CGROOT/memory.swap.current" > "$O/memory.swap.current" || true
[ -r "$CGROOT/memory.events" ] && cat "$CGROOT/memory.events" > "$O/memory.events" || true
exit "$rc"
