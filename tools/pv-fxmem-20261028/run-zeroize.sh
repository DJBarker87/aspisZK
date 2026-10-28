#!/bin/sh
set -eu
D=/home/dombarker/project-offloads/codex-pv-fxmem-20261028
R=/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu/bin/rustc
Z=/home/dombarker/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/zeroize-1.8.1/src/lib.rs
"$R" --version --verbose
"$R" -O --edition=2021 --crate-name zeroize --crate-type rlib "$Z" -o "$D/zeroize-04/libzeroize.rlib"
"$R" -O --edition=2021 "$D/zeroize-native.rs" --extern zeroize="$D/zeroize-04/libzeroize.rlib" -o "$D/zeroize-04/check"
"$D/zeroize-04/check"
