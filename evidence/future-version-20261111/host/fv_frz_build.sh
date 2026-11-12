#!/bin/bash
# Runs INSIDE a scope (fv_slot.sh). Aspis freeze: the verifier program built with the recipe of
# fv_build_adapter_src.sh, with the feature list and the two program identifiers the ELF embeds as
# parameters (the earlier script fixed them to the devnet Pool of the recorded payments).
# Usage: fv_frz_build.sh <attempt> <source-dir-name> <features> <pool-program-id> <registry-program-id>
# The source directory name also names the cargo target directory, so two source directories give two
# independent builds (different source path, different target path): that is the reproduction check.
# Time is expected in compilation (one SBF build, about two minutes on four cores).
set -u
W=/home/dombarker/project-offloads/future-version-20261111
A=$1; S=$2; FEATURES=$3; POOL=$4; REG=$5
T=/home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin/cargo-build-sbf
OUT=$W/out/$A; test ! -e $OUT || { echo "exists: $OUT"; exit 2; }
mkdir -p $OUT
ENVV=(HOME=/home/dombarker USER=dombarker PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_HOME=/home/dombarker/.cargo
  CARGO_TARGET_DIR=$W/target/sbf-frz-$S-$A CARGO_NET_OFFLINE=true "CARGO_TARGET_SBPF_SOLANA_SOLANA_RUSTFLAGS=-C link-arg=--threads=4" CARGO_BUILD_JOBS=4
  ASPIS_R1_POOL_PROGRAM_ID=$POOL ASPIS_R1_REGISTRY_PROGRAM_ID=$REG)
CMD=($T --manifest-path $W/$S/programs/r1-cost-probe/Cargo.toml --sbf-out-dir $OUT/artifacts --features $FEATURES --skip-tools-install --offline -j 4 -- --locked)
printf '%s\n' "${ENVV[@]}" > $OUT/env_exact.txt
printf '%s\n' "${CMD[@]}" > $OUT/cmd.txt
( cd $W/$S && find crates programs -name '*.rs' -o -name 'Cargo.toml' | sort | xargs sha256sum | sha256sum ) > $OUT/source_tree.sha256
( cd $W/$S && sha256sum Cargo.lock Cargo.toml ) > $OUT/lock.sha256
$T --version > $OUT/tool_version.txt 2>&1
cd $W/$S
taskset --cpu-list 0-3 env -i "${ENVV[@]}" "${CMD[@]}"
rc=$?
sha256sum $OUT/artifacts/*.so > $OUT/so.sha256 2>/dev/null
ls -l $OUT/artifacts/*.so > $OUT/so.size 2>/dev/null
cat $OUT/so.sha256
exit $rc
