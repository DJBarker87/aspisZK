#!/bin/bash
# X1b: cargo tests of the touched crates on a rewrite tree, release, offline, locked. Runs INSIDE one fv_slot.sh scope.
# Usage: fv_x1b_test.sh <tree dir under W/x1b> <step>...   steps: program (program crate lib tests, --features aspis),
# program2 (program crate lib tests, --features pool-adapter,private-leaf-salts: the two-transaction configuration),
# verifier, statement, core (deployed library features)
set -u
W=/home/dombarker/project-offloads/future-version-20261111; TREE=$1; shift; T=$W/x1b/$TREE
export PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_TARGET_DIR=$W/x1b/target/test-$TREE CARGO_NET_OFFLINE=true CARGO_BUILD_JOBS=4
export ASPIS_R1_POOL_PROGRAM_ID=4hxEyoU8MC3oFMya8D8MAcvhCPhLfHKDP1Ji9byYycn1 ASPIS_R1_REGISTRY_PROGRAM_ID=9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q
cd $T
for s in "$@"; do
  t0=$(date +%s)
  case $s in
    program) cargo test --locked --offline --release -p aspis-r1-cost-probe-program --features aspis --lib ;;
    program2) cargo test --locked --offline --release -p aspis-r1-cost-probe-program --features pool-adapter,private-leaf-salts --lib ;;
    verifier) cargo test --locked --offline --release -p aspis-r1-cost-probe --features aspis --lib ;;
    statement) cargo test --locked --offline --release -p aspis-statement --features r0,pool-v1-kernel --lib ;;
    core) cargo test --locked --offline --release -p aspis-core --features r0,fast-kmul,fast-prepared,fast-square,lazy-horner --lib ;;
  esac
  echo "STEP $s exit $? wall $(( $(date +%s) - t0 )) s"
done
