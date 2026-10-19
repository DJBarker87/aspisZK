#!/bin/bash
# c3/run-host-cols.sh <step> [args] : D72.2 focused Rust jobs in the branch workspace
# codex-r1p-column-writers-20261019 (r1p-retry/run-host.sh of D73 with this workspace), each in its
# own capped scope (MemoryHigh 6G, MemoryMax 8G, MemorySwapMax 0, TasksMax 64), optimized only.
# Expected time: build = compilation; test = proof generation + P_R1 checks + the column audit;
# gate = the same, repeated per attempt.
set -u
D=/home/dombarker/project-offloads/codex-r1p-column-writers-20261019
cd $D/repo || exit 2
STEP=$1; shift
TAG=${TAG:-$STEP}
export CARGO_TARGET_DIR=$D/target
run() {
  /usr/bin/time -v -o $D/time-$TAG.txt systemd-run --user --scope --quiet --unit=r1pcols-$TAG-$$ \
    -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 "$@"
}
echo "START $TAG $(date -Is) rev=$(cat $D/repo/REVISION 2>/dev/null)"
case $STEP in
  build)   run bash -c "~/.cargo/bin/cargo build --release --offline -j 4 -p aspis-r1-cost-probe --features r1p-check --lib --examples && ~/.cargo/bin/cargo test --release --offline -j 4 -p aspis-r1-cost-probe --features r1p-check --lib --no-run" ;;
  test)    run ~/.cargo/bin/cargo test --release --offline -j 4 -p aspis-r1-cost-probe --features r1p-check --lib "$@" -- --test-threads=1 --nocapture ;;
  gate)    run $D/target/release/examples/r1p_retry_gate "$@" ;;
  *) echo "unknown step"; exit 2 ;;
esac
rc=$?
echo "EXIT $rc $(date -Is)"
exit $rc
