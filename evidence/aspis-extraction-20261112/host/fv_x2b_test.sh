#!/bin/bash
# X2b: the Pool crate's tests on one tree (deployed feature list, release, offline, locked), then the X2b
# differential tests of the statement crate (filter x2b_, the statement crate's deployed feature pool-v1-kernel).
# Runs INSIDE one fv_slot.sh scope. Reads the tree; writes only the cargo target directory under W/x2b/target.
# Usage: fv_x2b_test.sh <tree dir> <target-name>
set -u
W=/home/dombarker/project-offloads/future-version-20261111
T=$1; N=$2
cd $T
E="env PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin RUSTUP_TOOLCHAIN=nightly-2026-09-17 CARGO_TARGET_DIR=$W/x2b/target/$N CARGO_NET_OFFLINE=true CARGO_BUILD_JOBS=4"
echo "== aspis-pool"
$E cargo test --release --offline --locked --manifest-path $T/programs/aspis-pool/Cargo.toml \
  --features r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit 2>&1
rc1=$?
echo "== aspis-statement x2b_"
$E cargo test --release --offline --locked --manifest-path $T/crates/aspis-statement/Cargo.toml --features pool-v1-kernel --lib x2b_ 2>&1
rc2=$?
echo "rc pool $rc1 statement $rc2"
[ $rc1 -eq 0 ] && [ $rc2 -eq 0 ]
