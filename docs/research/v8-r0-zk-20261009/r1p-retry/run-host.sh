#!/bin/bash
# r1p-retry/run-host.sh <step> [args] : focused Rust jobs for D38.3 (R-retry) and
# D44.3 (G-sim) on the build host, each in its own capped scope
# (MemoryHigh 6G, MemoryMax 8G, MemorySwapMax 0, TasksMax 64), optimized only.
# Expected time: build = compilation; test/simtest = proof generation, P_R1
# checks and simulation; gate/simgate = the same, repeated per attempt.
set -u
D=/home/dombarker/project-offloads/codex-r1p-retry-sim-20261019
cd $D/repo || exit 2
STEP=$1; shift
TAG=${TAG:-$STEP}
export CARGO_TARGET_DIR=$D/target
run() {
  /usr/bin/time -v -o $D/time-$TAG.txt systemd-run --user --scope --quiet --unit=r1p-$TAG-$$ \
    -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 "$@"
}
echo "START $TAG $(date -Is) rev=$(cat $D/repo/REVISION 2>/dev/null)"
case $STEP in
  build)   run bash -c "~/.cargo/bin/cargo build --release --offline -j 4 -p aspis-r1-cost-probe --features r1p-check --lib --examples && ~/.cargo/bin/cargo test --release --offline -j 4 -p aspis-r1-cost-probe --features r1p-check --lib --no-run" ;;
  test)    run ~/.cargo/bin/cargo test --release --offline -j 4 -p aspis-r1-cost-probe --features r1p-check --lib "$@" -- --test-threads=1 --nocapture ;;
  gate)    run $D/target/release/examples/r1p_retry_gate "$@" ;;
  simgate) run $D/target/release/examples/r1p_sim_gate "$@" ;;
  *) echo "unknown step"; exit 2 ;;
esac
rc=$?
echo "EXIT $rc $(date -Is)"
exit $rc
