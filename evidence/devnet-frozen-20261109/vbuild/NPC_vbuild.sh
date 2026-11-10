#!/bin/bash
# Usage: NPC_vbuild.sh <attempt> <mode default|devnet|retarget> <variant plain> (NOX_build.sh adapted: workspace path, retarget mode)
# Runs INSIDE the scope. FJd recipe: cargo-build-sbf 3.1.13, features pool-adapter,private-leaf-salts,
# --skip-tools-install --offline -j 4 -- --locked, fresh private CARGO_TARGET_DIR, no RUSTC_WRAPPER.
set -u
W=/home/dombarker/project-offloads/codex-cx-devnet2-20261109/vbuild
A=$1; MODE=$2; VAR=$3
T=/home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin/cargo-build-sbf
OUT=$W/out/$A; TGT=$W/target/$A
mkdir -p $OUT
test ! -e $TGT || { echo "target exists $TGT"; exit 2; }
ENVV=(HOME=/home/dombarker USER=dombarker PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_HOME=/home/dombarker/.cargo
  CARGO_TARGET_DIR=$TGT CARGO_NET_OFFLINE=true "CARGO_TARGET_SBPF_SOLANA_SOLANA_RUSTFLAGS=-C link-arg=--threads=4")
if [ "$VAR" = fjd ] || [ "$VAR" = fjdwrap ]; then ENVV+=(CARGO_PROFILE_RELEASE_BUILD_OVERRIDE_OPT_LEVEL=3); fi
if [ "$VAR" = wrapper ] || [ "$VAR" = fjdwrap ]; then ENVV+=(RUSTC_WRAPPER=$W/NOX_rustc_diagnostics.py S10_DIAGNOSTICS=$OUT/diagnostics); fi
if [ "$MODE" = devnet ]; then ENVV+=(ASPIS_R1_POOL_PROGRAM_ID=BmsNikL97uF7bb1hMnJxsas7a9LjjK8vvT5Q1b7W34Qs ASPIS_R1_REGISTRY_PROGRAM_ID=9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q); fi
# NPC_: retarget changes ONLY the Pool program id (new frozen-Pool program 37hdATMk...); registry id unchanged.
if [ "$MODE" = retarget ]; then ENVV+=(ASPIS_R1_POOL_PROGRAM_ID=37hdATMkskKX1hiCWhz4nnzkD7GauYwX8EQwcpUDb3Zt ASPIS_R1_REGISTRY_PROGRAM_ID=9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q); fi
CMD=($T --manifest-path $W/src/programs/r1-cost-probe/Cargo.toml --sbf-out-dir $OUT/artifacts --features pool-adapter,private-leaf-salts --skip-tools-install --offline -j 4 -- --locked)
printf '%s\n' "${ENVV[@]}" > $OUT/env_exact.txt
printf '%s\n' "${CMD[@]}" > $OUT/cmd.txt
cd $W/src
(cd $W/src && sha256sum Cargo.lock) > $OUT/lock_before.txt
# NPC_B003+: CPU affinity 0-3 (NKX fix for lld thread spawning under TasksMax=64); environment unchanged.
taskset --cpu-list 0-3 env -i "${ENVV[@]}" "${CMD[@]}" -v
rc=$?
(cd $W/src && sha256sum Cargo.lock) > $OUT/lock_after.txt
sha256sum $OUT/artifacts/*.so > $OUT/so.sha256 2>/dev/null
exit $rc
