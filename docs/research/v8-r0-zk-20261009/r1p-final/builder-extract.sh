#!/bin/sh
# Run only on the build host. No deployed source changes. Expected time is
# Rust compilation and Charon/Aeneas translation, not arithmetic generation.
set -eu
R=/home/dombarker/project-offloads/codex-cx-builder-ref-20261021
T=/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016
mkdir -p "$R/evidence" "$R/generated"
python3 - <<'PY'
from pathlib import Path
v=0
for p in Path('/sys/fs/cgroup').rglob('memory.max'):
    try:
        s=p.read_text().strip()
        if s != 'max' and (p.parent/'cgroup.procs').read_text().strip(): v+=int(s)
    except OSError: pass
print('populated MemoryMax bytes',v, 'requested',8*2**30,flush=True)
assert v+8*2**30 <= 55*2**30, 'host reservation exceeds 55 GiB'
PY
cat > "$R/source/Cargo.toml" <<'TOML'
[workspace]
members = ["crates/aspis-core", "crates/aspis-statement", "docs/research/v8-r0-zk-20261009/refine/writers", "docs/research/v8-r0-zk-20261009/refine/blockwriters", "docs/research/v8-r0-zk-20261009/refine/poseidon"]
resolver = "2"
[workspace.package]
edition = "2021"
license = "MIT OR Apache-2.0"
version = "0.1.0"
[workspace.dependencies]
aspis-core = { path = "crates/aspis-core" }
sha2 = "0.10.8"
TOML
cd "$R/source"
sha256sum "$T/charon-target/release/charon" "$T/bin/aeneas" > "$R/evidence/tool-sha256.txt"
set +e
systemd-run --user --scope --quiet -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 \
  --setenv=PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin --setenv=RUSTUP_TOOLCHAIN=nightly-2026-06-01 \
  /usr/bin/time -v -o "$R/evidence/charon-time.log" timeout 600 \
  "$T/charon-target/release/charon" cargo --preset aeneas --mir built \
  --start-from crate::pool_v1::pair_forest_trace::compile_pool_v1_pair_forest_private_transfer_merged_c1_v1 \
  --start-from crate::pool_v1::pair_forest_trace::compile_pool_v1_pair_forest_withdrawal_merged_c1_v1 \
  --dest-file "$R/evidence/compiler.llbc" -- --lib -p aspis-statement --release --offline -j 4 \
  > "$R/evidence/charon.log" 2>&1
ex=$?
printf 'charon exit=%s\n' "$ex"
if [ "$ex" -eq 0 ]; then
  systemd-run --user --scope --quiet -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 \
    /usr/bin/time -v -o "$R/evidence/aeneas-time.log" timeout 600 \
    "$T/bin/aeneas" -sequential -no-progress-bar -abort-on-error -backend lean \
    -namespace AspisShippedForestCompiler -dest "$R/generated" -loops-to-rec -print-unknown-externals \
    "$R/evidence/compiler.llbc" > "$R/evidence/aeneas.log" 2>&1
  printf 'aeneas exit=%s\n' "$?"
fi
tail -n 35 "$R/evidence/charon.log"
[ ! -e "$R/evidence/aeneas.log" ] || tail -n 35 "$R/evidence/aeneas.log"
grep -hE 'Elapsed|Maximum resident|Swaps|Exit status' "$R/evidence/"*-time.log
