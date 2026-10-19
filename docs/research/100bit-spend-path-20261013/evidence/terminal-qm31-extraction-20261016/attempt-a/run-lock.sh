#!/usr/bin/env bash
set -uo pipefail
cd /home/dombarker/project-offloads/aspis-r1-terminal-extraction-20261016/attempt-a/input
export PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin
export RUSTUP_TOOLCHAIN=nightly-2026-06-01
export CARGO_BUILD_JOBS=1
export CARGO_NET_OFFLINE=true
RID=lock-offline-a
OUT=../receipts/$RID
mkdir -p "$OUT"
start=$(date -u +%Y-%m-%dT%H:%M:%SZ); t0=$(date +%s.%N)
CG=$(awk -F: '$1=="0" {print $3}' /proc/self/cgroup); CGROOT=/sys/fs/cgroup$CG
printf "start=%s\ncgroup=%s\n" "$start" "$CGROOT" > "$OUT/metadata.txt"
sha256sum Cargo.lock > "$OUT/input-lock.sha256"
/usr/bin/time -v timeout 300s cargo generate-lockfile --offline > "$OUT/command.log" 2>&1
rc=$?
t1=$(date +%s.%N); end=$(date -u +%Y-%m-%dT%H:%M:%SZ)
printf "exit=%s\nend=%s\nwall_seconds=%s\n" "$rc" "$end" "$(awk -v a="$t0" -v b="$t1" BEGIN{printf %.3f,b-a})" >> "$OUT/metadata.txt"
sha256sum Cargo.lock > "$OUT/output-lock.sha256"
[ -r "$CGROOT/memory.peak" ] && cat "$CGROOT/memory.peak" > "$OUT/memory.peak" || true
[ -r "$CGROOT/memory.swap.current" ] && cat "$CGROOT/memory.swap.current" > "$OUT/memory.swap.current" || true
[ -r "$CGROOT/memory.events" ] && cat "$CGROOT/memory.events" > "$OUT/memory.events" || true
exit "$rc"
