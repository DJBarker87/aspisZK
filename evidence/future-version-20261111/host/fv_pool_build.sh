#!/bin/bash
# Runs INSIDE a scope (fv_slot.sh). Usage: fv_pool_build.sh <attempt> <source-dir-name>
# Builds the Aspis Pool with the recipe of the deployed Pool ELF (research
# evidence/pool-inventory2-20261109/NKZ_DEPLOYED_BUILD.json, attempt pool2): cargo-build-sbf 3.1.13,
# features r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit,
# -j 4, --locked, offline, the same CARGO_* environment. The recorded RUSTC_WRAPPER was a diagnostics
# logger and is not used here. Own target directory per source tree ($W/target/sbf-pool-<tree>).
# Time is expected in compilation (one SBF build of the Pool and its two Aspis crates).
set -u
W=/home/dombarker/project-offloads/future-version-20261111
A=$1; S=$2
FEATURES=r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit
T=/home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin/cargo-build-sbf
OUT=$W/out/$A; mkdir -p $OUT
ENVV=(HOME=/home/dombarker USER=dombarker PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_HOME=/home/dombarker/.cargo
  CARGO_TARGET_DIR=$W/target/sbf-pool-$S CARGO_NET_OFFLINE=true "CARGO_TARGET_SBPF_SOLANA_SOLANA_RUSTFLAGS=-C link-arg=--threads=4" CARGO_BUILD_JOBS=4)
CMD=($T --manifest-path $W/$S/programs/aspis-pool/Cargo.toml --sbf-out-dir $OUT/artifacts --features $FEATURES --skip-tools-install --offline -j 4 -- --locked)
printf '%s\n' "${ENVV[@]}" > $OUT/env_exact.txt
printf '%s\n' "${CMD[@]}" > $OUT/cmd.txt
( cd $W/$S && find crates/aspis-core crates/aspis-statement programs/aspis-pool -name '*.rs' -o -name 'Cargo.toml' | sort | xargs sha256sum; sha256sum Cargo.lock Cargo.toml ) > $OUT/source_files.sha256
cd $W/$S
taskset --cpu-list 0-3 env -i "${ENVV[@]}" "${CMD[@]}"
rc=$?
sha256sum $OUT/artifacts/*.so > $OUT/so.sha256 2>/dev/null
ls -l $OUT/artifacts/*.so > $OUT/so.size 2>/dev/null
exit $rc
