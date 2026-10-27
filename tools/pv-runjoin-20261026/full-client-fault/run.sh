#!/bin/sh
set -eu
cd /home/dombarker/project-offloads/codex-pv-runjoin-20261026/full-client-fault
export PATH="$HOME/.cargo/bin:$PATH"
# Expected work: optimized compilation; no proving/elimination body is entered.
/usr/bin/time -v -o build.time cargo build --offline --release -j 4 > build.log 2>&1
/usr/bin/time -v -o run.time ./target/release/pv-runjoin-full-client-fault retained-ledger > run.log 2>&1
sha256sum target/release/pv-runjoin-full-client-fault > binary.sha
wc -c < target/release/pv-runjoin-full-client-fault > binary.size
rustc -Vv > toolchain.txt
