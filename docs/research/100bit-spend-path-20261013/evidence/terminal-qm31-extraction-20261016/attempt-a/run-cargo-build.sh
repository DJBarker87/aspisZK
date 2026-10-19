#!/usr/bin/env bash
set -uo pipefail
BASE=/home/dombarker/project-offloads/aspis-r1-terminal-extraction-20261016/attempt-a
cd "$BASE/input"
export PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin
export RUSTUP_TOOLCHAIN=nightly-2026-06-01
export CARGO_BUILD_JOBS=1
export CARGO_NET_OFFLINE=true
export CARGO_TARGET_DIR="$BASE/cargo-target"
O="$BASE/receipts/cargo-build-a"; mkdir -p "$O"
start=$(date -u +%Y-%m-%dT%H:%M:%SZ); t0=$(date +%s%N)
CG=$(cut -d: -f3 /proc/self/cgroup); CGROOT=/sys/fs/cgroup$CG
printf 'start=%s\ncgroup=%s\ncommand=cargo build --package aspis-statement --features r0,pool-v1-kernel --no-default-features --release --lib --locked --offline\n' "$start" "$CGROOT" > "$O/metadata.txt"
sha256sum Cargo.toml Cargo.lock crates/aspis-core/Cargo.toml crates/aspis-statement/Cargo.toml > "$O/manifests.before.sha256"
/usr/bin/time -v timeout 300s cargo build --manifest-path Cargo.toml --package aspis-statement --features r0,pool-v1-kernel --no-default-features --release --lib --locked --offline > "$O/command.log" 2>&1
rc=$?
t1=$(date +%s%N); end=$(date -u +%Y-%m-%dT%H:%M:%SZ)
python3 - "$t0" "$t1" "$O/metadata.txt" "$rc" "$end" <<'PY'
import sys
s,e,path,rc,end=sys.argv[1:]
with open(path,"a") as f:f.write(f"exit={rc}\nend={end}\nwall_seconds={(int(e)-int(s))/1e9:.3f}\n")
PY
sha256sum Cargo.toml Cargo.lock crates/aspis-core/Cargo.toml crates/aspis-statement/Cargo.toml > "$O/manifests.after.sha256"
[ -r "$CGROOT/memory.peak" ] && cat "$CGROOT/memory.peak" > "$O/memory.peak" || true
[ -r "$CGROOT/memory.swap.current" ] && cat "$CGROOT/memory.swap.current" > "$O/memory.swap.current" || true
[ -r "$CGROOT/memory.events" ] && cat "$CGROOT/memory.events" > "$O/memory.events" || true
find "$CARGO_TARGET_DIR/release" -maxdepth 2 -type f -name 'libaspis_statement*' -o -name 'aspis_statement-*' 2>/dev/null | sort > "$O/artifacts.txt"
while IFS= read -r f; do [ -f "$f" ] && sha256sum "$f"; done < "$O/artifacts.txt" > "$O/artifact-hashes.sha256"
exit "$rc"
