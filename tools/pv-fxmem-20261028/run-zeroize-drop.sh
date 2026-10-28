#!/bin/sh
set -eu
D=/home/dombarker/project-offloads/codex-pv-fxmem-20261028
R=/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu/bin/rustc
sha256sum "$D/zeroize-04/libzeroize.rlib"
"$R" -O --edition=2021 "$D/zeroize-drop.rs" --extern zeroize="$D/zeroize-04/libzeroize.rlib" -o "$D/zeroize-drop-06/check"
"$D/zeroize-drop-06/check"
