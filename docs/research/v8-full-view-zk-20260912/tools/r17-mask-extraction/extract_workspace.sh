#!/usr/bin/env bash
set -euo pipefail
# Bounded, zero-swap Linux scope. One optimized dependency-free extraction.
inputs=${1:?pinned original source directory}
candidate=${2:?r17_mask_workspace.rs}
expected=${3:?recorded candidate SHA256}
task=${4:?fresh output directory}
kit=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
charon=/home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon/bin/charon
test "$(sha256sum "$charon" | cut -d' ' -f1)" = b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c
test "$(sha256sum "$inputs/field.rs" | cut -d' ' -f1)" = 5795495e2fa9ad85e097c2ad96ffc826aaad3c16afc0e0bd00459f9f51068cd8
test "$(sha256sum "$inputs/r17_structured_g.rs" | cut -d' ' -f1)" = 147be74e8651e05aa4680dbb412252751e8f21f5a6ad8a4de939d0f01bfb52c6
test "$(sha256sum "$candidate" | cut -d' ' -f1)" = "$expected"
test ! -e "$task"
mkdir -p "$task/source" "$task/output"
cp "$kit/Cargo.toml" "$task/source/"
cp "$kit/workspace_lib.rs" "$task/source/lib.rs"
cp "$inputs/field.rs" "$inputs/r17_structured_g.rs" "$candidate" "$task/source/"
export PATH=/home/dombarker/.cargo/bin:$PATH
export RUSTUP_TOOLCHAIN=nightly-2026-06-01
export CARGO_BUILD_JOBS=1
export CARGO_TARGET_DIR="$task/target"
cd "$task/source"
cargo generate-lockfile --offline
sha256sum Cargo.toml Cargo.lock lib.rs field.rs r17_structured_g.rs r17_mask_workspace.rs
exec /usr/bin/time -v "$charon" cargo --preset aeneas --mir built \
  --sysroot default --start-from crate::r17_mask_workspace::mask_weights_into \
  --dest-file "$task/output/R17MaskWorkspace.llbc" -- \
  --locked --offline --release --lib --no-default-features
