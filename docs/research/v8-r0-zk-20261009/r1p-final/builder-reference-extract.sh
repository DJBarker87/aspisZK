#!/bin/sh
# Focused host translation of a proof-only indexed reference, with source pins.
set -eu
R=/home/dombarker/project-offloads/codex-cx-builder-ref2-20261021
T=/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016
MODE=${1:-poseidon}
case "$MODE" in
 poseidon) ENTRY=crate::poseidon2::builder_reference::external_reference ;;
 owned) ENTRY=crate::poseidon2::builder_reference::external_owned ;;
 records|records-indexed|records-owned|records-owned-u32) ENTRY=crate::pool_v1::pair_forest_copy_builder::records_reference::records_reference_with_roots ;;
 *) exit 64 ;;
esac
E=$R/continuation3/extract-$MODE
mkdir -p "$E/generated"
test ! -e "$E/charon.log"
cd "$R/source"
export PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin RUSTUP_TOOLCHAIN=nightly-2026-06-01
export RUSTFLAGS='-C link-arg=-Wl,--threads=4 --cfg aeneas_ref'
export CARGO_TARGET_DIR="$R/reference-target"
python3 - <<'PY'
from pathlib import Path
reserved=0
for p in Path('/sys/fs/cgroup').rglob('memory.max'):
    try:
        v=p.read_text().strip()
        if v!='max' and (p.parent/'cgroup.procs').read_text().strip():reserved+=int(v)
    except OSError:pass
print('reserved',reserved,'expected: proof-reference compilation/translation',flush=True)
assert reserved+8*2**30<=55*2**30
PY
systemd-run --user --scope --quiet -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 \
  /usr/bin/time -v -o "$E/charon-time.log" timeout 120 \
  "$T/charon-target/release/charon" cargo --preset aeneas --mir built \
  --start-from "$ENTRY" --include 'aspis_core::field::*' \
  --dest-file "$E/reference.llbc" -- --lib -p aspis-statement --release --offline -j 4 \
  > "$E/charon.log" 2>&1
systemd-run --user --scope --quiet -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 \
  /usr/bin/time -v -o "$E/aeneas-time.log" timeout 120 \
  "$T/bin/aeneas" -sequential -no-progress-bar -abort-on-error -backend lean \
  -namespace AspisBuilderPoseidonReference -dest "$E/generated" -loops-to-rec -print-unknown-externals \
  "$E/reference.llbc" > "$E/aeneas.log" 2>&1
