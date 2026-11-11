#!/bin/bash
# Runs INSIDE a scope. Usage: fv_build.sh <attempt> <features>
# Recipe of docs/r1/BUILD.md (cargo-build-sbf 3.1.13, platform-tools v1.52, offline, locked, -j 4),
# WITHOUT pool-adapter: the three-account measurement entry. Shared target directory across variants.
set -u
W=/home/dombarker/project-offloads/future-version-20261111
A=$1; FEATURES=$2
T=/home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin/cargo-build-sbf
OUT=$W/out/$A; mkdir -p $OUT
ENVV=(HOME=/home/dombarker USER=dombarker PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_HOME=/home/dombarker/.cargo
  CARGO_TARGET_DIR=$W/target/sbf CARGO_NET_OFFLINE=true "CARGO_TARGET_SBPF_SOLANA_SOLANA_RUSTFLAGS=-C link-arg=--threads=4" CARGO_BUILD_JOBS=4)
CMD=($T --manifest-path $W/src/programs/r1-cost-probe/Cargo.toml --sbf-out-dir $OUT/artifacts --features $FEATURES --skip-tools-install --offline -j 4 -- --locked)
printf '%s\n' "${ENVV[@]}" > $OUT/env_exact.txt
printf '%s\n' "${CMD[@]}" > $OUT/cmd.txt
cd $W/src
sha256sum Cargo.lock > $OUT/lock_before.txt
taskset --cpu-list 0-3 env -i "${ENVV[@]}" "${CMD[@]}"
rc=$?
sha256sum Cargo.lock > $OUT/lock_after.txt
sha256sum $OUT/artifacts/*.so > $OUT/so.sha256 2>/dev/null
ls -l $OUT/artifacts/*.so > $OUT/so.size 2>/dev/null
exit $rc
