#!/bin/bash
# r1p-retry/run-host-pole.sh <step> [args] : focused Rust jobs for LOG D73.4
# items 1 and 2 (pole and mask exhaustion as rejected attempts) on the build
# host, each in its own capped scope (MemoryHigh 6G, MemoryMax 8G,
# MemorySwapMax 0, TasksMax 64), optimized only.
# Expected time: build = compilation; test = proof generation (about 5.5 s
# per attempt) plus, for the real-check test only, the P_R1 check (about 36 s
# per attempt).
set -u
D=/home/dombarker/project-offloads/codex-r1p-pole-retry-20261019
cd $D/repo || exit 2
STEP=$1; shift
TAG=${TAG:-$STEP}
export CARGO_TARGET_DIR=$D/target
run() {
  /usr/bin/time -v -o $D/time-$TAG.txt systemd-run --user --scope --quiet --unit=r1p-pole-$TAG-$$ \
    -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 "$@"
}
echo "START $TAG $(date -Is) rev=$(cat $D/repo/REVISION 2>/dev/null)"
case $STEP in
  build)  run bash -c "~/.cargo/bin/cargo test --release --offline -j 4 -p aspis-r1-cost-probe --features r1p-check --lib --no-run" ;;
  check)  run bash -c "~/.cargo/bin/cargo check --release --offline -j 4 -p aspis-r1-cost-probe --lib && ~/.cargo/bin/cargo check --release --offline -j 4 -p aspis-r1-cost-probe --features prover,private-leaf-salts --lib" ;;
  test)   run ~/.cargo/bin/cargo test --release --offline -j 4 -p aspis-r1-cost-probe --features r1p-check --lib "$@" -- --test-threads=1 --nocapture ;;
  *) echo "unknown step"; exit 2 ;;
esac
rc=$?
echo "EXIT $rc $(date -Is)"
exit $rc
