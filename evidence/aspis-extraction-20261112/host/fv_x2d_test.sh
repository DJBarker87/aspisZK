#!/bin/bash
# X2d (copy of fv_x2c_test.sh, outputs under W/x2d): the Pool crate's tests on one tree (deployed feature list,
# release, offline, locked), then every test of pair_forest::tests again, one process per test, with the
# handler-state recorder on (X2C_STATE_DUMP). The statement crate is unchanged by X2d and is not run.
# Runs INSIDE one fv_slot.sh scope. Time is expected in compilation, then about a minute of tests.
# Usage: fv_x2d_test.sh <tree dir> <target-name> <dump dir>
set -u
W=/home/dombarker/project-offloads/future-version-20261111
T=$1; N=$2; D=$3
mkdir -p $D
cd $T
E="env PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin RUSTUP_TOOLCHAIN=nightly-2026-09-17 CARGO_TARGET_DIR=$W/x2d/target/$N CARGO_NET_OFFLINE=true CARGO_BUILD_JOBS=4"
FEAT=r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit
echo "== aspis-pool"
$E cargo test --release --offline --locked --manifest-path $T/programs/aspis-pool/Cargo.toml --features $FEAT 2>&1
rc1=$?
echo "== recorder runs"
BIN=$($E cargo test --release --offline --locked --manifest-path $T/programs/aspis-pool/Cargo.toml --features $FEAT --no-run --message-format=json 2>/dev/null | python3 -c 'import sys,json
for l in sys.stdin:
    try: m=json.loads(l)
    except Exception: continue
    if m.get("reason")=="compiler-artifact" and m.get("executable") and m["target"]["name"]=="aspis_pool" and m["profile"].get("test"): print(m["executable"])' | tail -1)
echo "bin $BIN"
for t in $($BIN --list 2>/dev/null | sed -n 's/^\(pair_forest::tests::[^:]*\): test$/\1/p'); do
  X2C_STATE_DUMP=$D $BIN --exact $t --test-threads=1 > /dev/null 2>&1; echo "$t $?"
done > $D/exit-codes.txt
echo "recorded $(ls $D | wc -l) files"
echo "rc pool $rc1"
[ $rc1 -eq 0 ]
