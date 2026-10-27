#!/bin/sh
set -eu
cd /home/dombarker/project-offloads/codex-pv-runjoin-20261026
export PATH="$HOME/.cargo/bin:$PATH"
python3 reservation-existing.py evidence/native-repeat-go.json --requested-bytes 0
/usr/bin/time -v -o evidence/native-repeat-build.time cargo build --offline --release -j 4 > evidence/native-repeat-build.log 2>&1
/usr/bin/time -v -o evidence/native-repeat-run.time ./target/release/pv-runjoin-native-repeat > evidence/native-repeat-run.log 2>&1
sha256sum target/release/pv-runjoin-native-repeat > evidence/native-repeat-bin.sha
wc -c < target/release/pv-runjoin-native-repeat > evidence/native-repeat-bin.size
rustc --version > evidence/native-repeat-toolchain.txt
