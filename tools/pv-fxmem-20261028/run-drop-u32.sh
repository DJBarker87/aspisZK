#!/bin/sh
set -eu
D=/home/dombarker/project-offloads/codex-pv-fxmem-20261028
R=/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu/bin/rustc
"$R" --version --verbose
"$R" -O -C panic=unwind --edition=2021 "$D/drop-u32.rs" -o "$D/drop-u32-03/check"
"$D/drop-u32-03/check"
