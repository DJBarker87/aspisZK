#!/bin/sh
set -eu
D=/home/dombarker/project-offloads/codex-pv-fxmem-20261028
R=/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu/bin/rustc
"$R" --version --verbose
"$R" -O --edition=2021 "$D/reserve-native.rs" -o "$D/reserve-05/check"
"$D/reserve-05/check"
