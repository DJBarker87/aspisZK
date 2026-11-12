#!/bin/bash
# X1 stage 2: cargo tests of the touched crates on the rewrite tree, inside ONE fv_slot.sh scope. Usage: fv_x1_test.sh <step>...
# steps: core (aspis-core lib tests, deployed core features, release), core-exhaustive (the ignored exhaustive CM31/M31
# inverse comparison, release), program (program crate lib tests with --features aspis, release)
set -u
W=/home/dombarker/project-offloads/future-version-20261111; T=$W/x1/${X1_TREE:-rw-tree}
export PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_TARGET_DIR=$W/x1/target/test-${X1_TREE:-rw-tree} CARGO_NET_OFFLINE=true CARGO_BUILD_JOBS=4
cd $T
for s in "$@"; do
  t0=$(date +%s)
  case $s in
    core) cargo test --locked --offline --release -p aspis-core --features r0,fast-kmul,fast-prepared,fast-square,lazy-horner --lib ;;
    core-exhaustive) cargo test --locked --offline --release -p aspis-core --features r0,fast-kmul,fast-prepared,fast-square,lazy-horner --lib x1_cm31_inv_rewrite -- --ignored ;;
    program) cargo test --locked --offline --release -p aspis-r1-cost-probe-program --features aspis --lib ;;
    verifier) cargo test --locked --offline --release -p aspis-r1-cost-probe --lib ;;
    statement) cargo test --locked --offline --release -p aspis-statement --features r0,pool-v1-kernel --lib ;;
  esac
  echo "STEP $s exit $? wall $(( $(date +%s) - t0 )) s"
done
