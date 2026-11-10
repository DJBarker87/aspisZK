#!/bin/bash
# NPK_ build driver; runs INSIDE the capped scope.
# Usage: NPK_build.sh <attempt> <mode default|devnet|retarget|pool>
# Verifier recipe = NOX_B002/B003 (cargo-build-sbf 3.1.13, pool-adapter,private-leaf-salts, env -i, no wrapper,
# no CARGO_PROFILE_RELEASE_BUILD_OVERRIDE_OPT_LEVEL); retarget = NPC_B002 (Pool id 37hdATMk...).
# Pool recipe = NKX pool1 features under the same env -i shape. -v logs rustc command lines only.
# The target directory is kept (dep-info is the product of this job).
set -u
W=/home/dombarker/project-offloads/codex-cx-cone-20261110
A=$1; MODE=$2
T=/home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin/cargo-build-sbf
OUT=$W/out/$A; TGT=$W/target/$A
mkdir -p $OUT/artifacts
test ! -e $TGT || { echo "target exists $TGT"; exit 2; }
if [ "$MODE" = pool ]; then SRC=$W/src-p; PROG=aspis-pool; KEY=aspis_pool-keypair.json
  FEAT=r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit
else SRC=$W/src-v; PROG=r1-cost-probe; KEY=aspis_r1_cost_probe_program-keypair.json; FEAT=pool-adapter,private-leaf-salts; fi
# Directory placeholder: cargo-build-sbf skips key generation when this path exists; no key is created or read.
mkdir -p $OUT/artifacts/$KEY
ENVV=(HOME=/home/dombarker USER=dombarker PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_HOME=/home/dombarker/.cargo
  CARGO_TARGET_DIR=$TGT CARGO_NET_OFFLINE=true "CARGO_TARGET_SBPF_SOLANA_SOLANA_RUSTFLAGS=-C link-arg=--threads=4")
if [ "$MODE" = devnet ]; then ENVV+=(ASPIS_R1_POOL_PROGRAM_ID=BmsNikL97uF7bb1hMnJxsas7a9LjjK8vvT5Q1b7W34Qs ASPIS_R1_REGISTRY_PROGRAM_ID=9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q); fi
if [ "$MODE" = retarget ]; then ENVV+=(ASPIS_R1_POOL_PROGRAM_ID=37hdATMkskKX1hiCWhz4nnzkD7GauYwX8EQwcpUDb3Zt ASPIS_R1_REGISTRY_PROGRAM_ID=9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q); fi
CMD=($T --manifest-path $SRC/programs/$PROG/Cargo.toml --sbf-out-dir $OUT/artifacts --features $FEAT --skip-tools-install --offline -j 4 -- --locked)
printf '%s\n' "${ENVV[@]}" > $OUT/env_exact.txt
printf '%s\n' "${CMD[@]}" -v > $OUT/cmd.txt
sha256sum $T /home/dombarker/.cache/solana/v1.52/platform-tools/rust/bin/rustc > $OUT/tool_sha256.txt
cd $SRC
sha256sum Cargo.lock > $OUT/lock_before.txt
env -i "${ENVV[@]}" taskset --cpu-list 0-3 "${CMD[@]}" -v
rc=$?
sha256sum Cargo.lock > $OUT/lock_after.txt
sha256sum $OUT/artifacts/*.so > $OUT/so.sha256 2>/dev/null
exit $rc
