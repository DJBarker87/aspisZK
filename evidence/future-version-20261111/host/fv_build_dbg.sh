#!/bin/bash
# Runs INSIDE a scope. Usage: fv_build_dbg.sh <attempt> <features>
# Same recipe as fv_build.sh plus DWARF line tables, in its own target directory.
# The stripped output must hash-equal the matching non-debug build to be used.
set -u
W=/home/dombarker/project-offloads/future-version-20261111
A=$1; FEATURES=$2
T=/home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin/cargo-build-sbf
OUT=$W/out/$A; mkdir -p $OUT
ENVV=(HOME=/home/dombarker USER=dombarker PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_HOME=/home/dombarker/.cargo
  CARGO_TARGET_DIR=$W/target/sbf-dbg-$A CARGO_NET_OFFLINE=true "CARGO_TARGET_SBPF_SOLANA_SOLANA_RUSTFLAGS=-C link-arg=--threads=4" CARGO_BUILD_JOBS=4
  CARGO_PROFILE_RELEASE_DEBUG=line-tables-only)
CMD=($T --manifest-path $W/src/programs/r1-cost-probe/Cargo.toml --sbf-out-dir $OUT/artifacts --features $FEATURES --skip-tools-install --offline -j 4 -- --locked)
printf '%s\n' "${ENVV[@]}" > $OUT/env_exact.txt
printf '%s\n' "${CMD[@]}" > $OUT/cmd.txt
cd $W/src
taskset --cpu-list 0-3 env -i "${ENVV[@]}" "${CMD[@]}"
rc=$?
sha256sum $OUT/artifacts/*.so > $OUT/so.sha256 2>/dev/null
cp $W/target/sbf-dbg-$A/sbpf-solana-solana/release/aspis_r1_cost_probe_program.so $OUT/linked-unstripped.so 2>/dev/null
exit $rc
