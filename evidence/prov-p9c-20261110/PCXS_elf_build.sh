#!/bin/bash
# Runs INSIDE the scope (host). Usage: PCXS_elf_build.sh <attempt> <mode default|retarget> <pkg r1|upload>
# Recipe = NPC_vbuild.sh (cargo-build-sbf 3.1.13, --skip-tools-install --offline -j 4 -- --locked, fresh CARGO_TARGET_DIR,
# taskset 0-3 outside env -i, no RUSTC_WRAPPER). Workspace moved to the PIN2 workspace.
set -u
W=/home/dombarker/project-offloads/codex-pc-pin2-elf-20261111
A=$1; MODE=$2; PKG=$3
T=/home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin/cargo-build-sbf
OUT=$W/out/$A; TGT=$W/target/$A
mkdir -p $OUT
test ! -e $TGT || { echo "target exists $TGT"; exit 2; }
ENVV=(HOME=/home/dombarker USER=dombarker PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_HOME=/home/dombarker/.cargo
  CARGO_TARGET_DIR=$TGT CARGO_NET_OFFLINE=true "CARGO_TARGET_SBPF_SOLANA_SOLANA_RUSTFLAGS=-C link-arg=--threads=4" CARGO_BUILD_JOBS=4)
if [ "$MODE" = retarget ]; then ENVV+=(ASPIS_R1_POOL_PROGRAM_ID=37hdATMkskKX1hiCWhz4nnzkD7GauYwX8EQwcpUDb3Zt ASPIS_R1_REGISTRY_PROGRAM_ID=9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q); fi
if [ "$PKG" = r1 ]; then
  CMD=($T --manifest-path $W/src/programs/r1-cost-probe/Cargo.toml --sbf-out-dir $OUT/artifacts --features pool-adapter,private-leaf-salts --skip-tools-install --offline -j 4 -- --locked)
else
  CMD=($T --manifest-path $W/src/programs/aspis-upload/Cargo.toml --sbf-out-dir $OUT/artifacts --skip-tools-install --offline -j 4 -- --locked)
fi
printf '%s\n' "${ENVV[@]}" > $OUT/env_exact.txt
printf '%s\n' "${CMD[@]}" > $OUT/cmd.txt
cd $W/src
sha256sum Cargo.lock > $OUT/lock_before.txt
taskset --cpu-list 0-3 env -i "${ENVV[@]}" "${CMD[@]}" -v
rc=$?
sha256sum Cargo.lock > $OUT/lock_after.txt
sha256sum $OUT/artifacts/*.so > $OUT/so.sha256 2>/dev/null
ls -l $OUT/artifacts/*.so > $OUT/so.size 2>/dev/null
exit $rc
