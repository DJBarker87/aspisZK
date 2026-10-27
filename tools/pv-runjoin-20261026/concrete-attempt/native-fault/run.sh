#!/bin/sh
set -eu
cd /home/dombarker/project-offloads/codex-pv-runjoin-20261026/native-fault
export PATH="$HOME/.cargo/bin:$PATH"
# Time is expected in tiny optimized compilation, then one filtered syscall.
/usr/bin/time -v -o build-02.time cargo build --offline --release -j 4 > build-02.log 2>&1
/usr/bin/time -v -o run-02.time ./target/release/pv-runjoin-native-fault > run-02.log 2>&1
sha256sum target/release/pv-runjoin-native-fault > binary.sha
wc -c < target/release/pv-runjoin-native-fault > binary.size
rustc -Vv > toolchain.txt
