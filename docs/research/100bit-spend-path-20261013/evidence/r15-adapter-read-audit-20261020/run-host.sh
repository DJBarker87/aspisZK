#!/bin/sh
set -eu
TASK=/home/dombarker/project-offloads/codex-cx-adapter-audit2-20261020
export PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin
export CARGO_HOME=/home/dombarker/.cargo CARGO_NET_OFFLINE=true
export CARGO_TARGET_DIR=$TASK/native-target CARGO_BUILD_JOBS=4
export RUSTFLAGS="-C link-arg=-Wl,--threads=4"
python3 "$TASK/harness/reservation.py" "$TASK/reservation.json"
cd "$TASK/src"
exec systemd-run --user --scope --unit=r15-adapter-read-audit-20261020 \
  -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 \
  python3 "$TASK/harness/capped.py" "$TASK/receipts/read-teeth" \
  "Incremental release compilation and two account-read tests; no proof generation or elimination" -- \
  cargo test --release --offline --locked -j 4 -p aspis-r1-cost-probe-program \
  --features pool-adapter,private-leaf-salts --lib r15_read_ -- --test-threads=1
