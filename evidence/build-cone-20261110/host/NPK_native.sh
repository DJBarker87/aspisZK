#!/bin/bash
# NPK_ host-target dep-info for the extraction configurations; runs INSIDE the capped scope.
# Usage: NPK_native.sh <attempt> <manifest-rel> <features>
# Toolchain = the Charon driver's nightly-2026-06-01 (Charon cargo --release --lib --locked --offline).
# Source = src-x: the 658-file NHR staged extraction workspace (PCO_E001/sources/NHR_STAGING_MANIFEST.json), blobs by git id.
# cargo check emits dep-info for every unit (same files opened by the front end); no Charon/Aeneas run here.
set -u
W=/home/dombarker/project-offloads/codex-cx-cone-20261110
A=$1; M=$2; F=$3
OUT=$W/out/$A; TGT=$W/target/$A; SRC=$W/${NPK_SRC:-src-x}
mkdir -p $OUT; test ! -e $TGT || { echo "target exists $TGT"; exit 2; }
ENVV=(HOME=/home/dombarker USER=dombarker PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_HOME=/home/dombarker/.cargo
  RUSTUP_TOOLCHAIN=nightly-2026-06-01-x86_64-unknown-linux-gnu CARGO_TARGET_DIR=$TGT CARGO_NET_OFFLINE=true)
CMD=(cargo check --manifest-path $SRC/$M --locked --offline --release --lib -j 4 --features $F -v)
printf '%s\n' "${ENVV[@]}" > $OUT/env_exact.txt; printf '%s\n' "${CMD[@]}" > $OUT/cmd.txt
cd $SRC; sha256sum Cargo.lock > $OUT/lock_before.txt
env -i "${ENVV[@]}" "${CMD[@]}"; rc=$?
sha256sum Cargo.lock > $OUT/lock_after.txt
exit $rc
