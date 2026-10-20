#!/bin/sh
set -eu
TASK=/home/dombarker/project-offloads/codex-cx-adapter-audit-20261020
export PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin
export CARGO_HOME=/home/dombarker/.cargo CARGO_NET_OFFLINE=true
export CARGO_TARGET_DIR=$TASK/native-target CARGO_BUILD_JOBS=4
export RUSTFLAGS="-C link-arg=-Wl,--threads=4"
python3 "$TASK/harness/reservation.py" "$TASK/reservation-program-lib-path-fixed.json"
cd "$TASK/src"
exec systemd-run --user --scope --unit=r15-adapter-audit-path-fixed-20261020 \
  -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 \
  python3 "$TASK/harness/capped.py" "$TASK/receipts/program-lib-path-fixed" \
  "Incremental release compilation and saved-fixture account tests; no proof generation or elimination" -- \
  cargo test --release --offline --locked -j 4 -p aspis-r1-cost-probe-program \
  --features pool-adapter,private-leaf-salts --lib -- --test-threads=1
