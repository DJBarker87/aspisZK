#!/bin/bash
# X2 stage 2: the Pool crate's tests on one tree, deployed feature list, release, offline, locked. Runs INSIDE one
# fv_slot.sh scope. Reads the tree; writes only the cargo target directory under W/x2/target.
# Usage: fv_x2_test.sh <tree dir> <target-name>
set -u
W=/home/dombarker/project-offloads/future-version-20261111
T=$1; N=$2
cd $T
env PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin RUSTUP_TOOLCHAIN=nightly-2026-09-17 CARGO_TARGET_DIR=$W/x2/target/$N CARGO_NET_OFFLINE=true CARGO_BUILD_JOBS=4 \
  cargo test --release --offline --locked --manifest-path $T/programs/aspis-pool/Cargo.toml \
  --features r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit 2>&1
