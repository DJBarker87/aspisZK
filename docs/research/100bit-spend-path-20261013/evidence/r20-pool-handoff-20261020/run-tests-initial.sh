#!/bin/sh
set -eu
H=/home/dombarker/project-offloads/codex-cx-r20-pool-20261020
export PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin
export CARGO_TARGET_DIR=$H/test-target CARGO_BUILD_JOBS=4
export RUSTFLAGS='-C link-arg=-Wl,--threads=4'
python3 "$H/harness/reservation.py" "$H/reservation-tests.json" >/dev/null
exec "$H/harness/capped-run.sh" pool-lib-tests \
 'Release compilation then AccountInfo and handoff unit tests; no proof generation or elimination' \
 "$H/test-src" -- cargo test --release --offline --locked -j 4 -p aspis-pool \
 --features r1-split-checkpoint,pair-forest-direct-result-audit --lib -- --test-threads=1
