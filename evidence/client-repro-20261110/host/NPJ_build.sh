#!/bin/bash
# NPJ_ attempt $1: build dfa35acd devnet_spend with the recorded NDZ command.
set -u
W=/home/dombarker/project-offloads/codex-cx-client-20261110
ORIG=/home/dombarker/project-offloads/codex-cx-devnet-rehearse-20261029/NDZ_src
N=$1
cd $W
export PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin
export CARGO_TARGET_DIR=$W/target-$N
export RUSTFLAGS="--remap-path-prefix=$W/NDZ_src=$ORIG"
unset CARGO_BUILD_RUSTFLAGS CARGO_ENCODED_RUSTFLAGS
env | grep -E "^(RUST|CARGO)" | sort > receipts/NPJ_attempt$N.env
rustc -vV > receipts/NPJ_attempt$N.rustc; cargo -vV > receipts/NPJ_attempt$N.cargo
timeout 1800 systemd-run --user --scope --unit=NPJ-client-build$N -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 \
  /usr/bin/time -v -o receipts/NPJ_attempt$N.time \
  cargo build --manifest-path NDZ_src/tools/r1-cost-probe/Cargo.toml --release --locked --offline -j ${JOBS:-4} --features r1p-check --bin devnet_spend \
  > receipts/NPJ_attempt$N.log 2>&1
echo "exit=$?" > receipts/NPJ_attempt$N.exit
sha256sum $CARGO_TARGET_DIR/release/devnet_spend >> receipts/NPJ_attempt$N.exit 2>&1
