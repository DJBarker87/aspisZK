#!/bin/bash
# Usage: NOX_build.sh <attempt> <mode default|devnet> <variant fjd|wrapper>
# Runs INSIDE the scope. FJd recipe: cargo-build-sbf 3.1.13, features pool-adapter,private-leaf-salts,
# --skip-tools-install --offline -j 4 -- --locked, fresh private CARGO_TARGET_DIR, no RUSTC_WRAPPER.
set -u
W=/home/dombarker/project-offloads/codex-cx-l188-20261109
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
CMD=($T --manifest-path $W/src/programs/r1-cost-probe/Cargo.toml --sbf-out-dir $OUT/artifacts --features pool-adapter,private-leaf-salts --skip-tools-install --offline -j 4 -- --locked)
printf '%s\n' "${ENVV[@]}" > $OUT/env_exact.txt
printf '%s\n' "${CMD[@]}" > $OUT/cmd.txt
cd $W/src
(cd $W/src && sha256sum Cargo.lock) > $OUT/lock_before.txt
env -i "${ENVV[@]}" "${CMD[@]}" -v
rc=$?
(cd $W/src && sha256sum Cargo.lock) > $OUT/lock_after.txt
sha256sum $OUT/artifacts/*.so > $OUT/so.sha256 2>/dev/null
exit $rc
