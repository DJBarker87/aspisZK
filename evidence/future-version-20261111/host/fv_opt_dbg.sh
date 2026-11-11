#!/bin/bash
# Runs INSIDE a scope. Usage: fv_opt_dbg.sh <attempt> <features> <source-dir-name>
# fv_build_adapter_src.sh plus DWARF line tables, own target directory per source tree
# (target/sbf-dbg-<tree>). For register-trace attribution only. The stripped output is compared
# with the non-debug build of the same source; it is used only if the hashes are equal.
set -u
W=/home/dombarker/project-offloads/future-version-20261111
A=$1; FEATURES=$2; S=$3
T=/home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin/cargo-build-sbf
OUT=$W/out/$A; mkdir -p $OUT
ENVV=(HOME=/home/dombarker USER=dombarker PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_HOME=/home/dombarker/.cargo
  CARGO_TARGET_DIR=$W/target/sbf-dbg-$S CARGO_NET_OFFLINE=true "CARGO_TARGET_SBPF_SOLANA_SOLANA_RUSTFLAGS=-C link-arg=--threads=4" CARGO_BUILD_JOBS=4
  CARGO_PROFILE_RELEASE_DEBUG=line-tables-only
  ASPIS_R1_POOL_PROGRAM_ID=37hdATMkskKX1hiCWhz4nnzkD7GauYwX8EQwcpUDb3Zt ASPIS_R1_REGISTRY_PROGRAM_ID=9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q)
CMD=($T --manifest-path $W/$S/programs/r1-cost-probe/Cargo.toml --sbf-out-dir $OUT/artifacts --features $FEATURES --skip-tools-install --offline -j 4 -- --locked)
printf '%s\n' "${ENVV[@]}" > $OUT/env_exact.txt
printf '%s\n' "${CMD[@]}" > $OUT/cmd.txt
cd $W/$S
taskset --cpu-list 0-3 env -i "${ENVV[@]}" "${CMD[@]}"
rc=$?
sha256sum $OUT/artifacts/*.so > $OUT/so.sha256 2>/dev/null
cp $W/target/sbf-dbg-$S/sbpf-solana-solana/release/aspis_r1_cost_probe_program.so $OUT/linked-unstripped.so 2>/dev/null
exit $rc
