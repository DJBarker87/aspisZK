#!/bin/sh
set -eu
D=/home/dombarker/project-offloads/codex-pv-fxio-20261028
/home/dombarker/.cargo/bin/rustc +nightly-2026-06-01 --version --verbose
/home/dombarker/.cargo/bin/rustc +nightly-2026-06-01 -O --edition=2021 "$D/native-repeat.rs" -o "$D/native-repeat"
"$D/native-repeat" "$D/native-fixture-01"
