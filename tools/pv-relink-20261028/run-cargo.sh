#!/bin/sh
set -eu
row="$1"
d=/home/dombarker/project-offloads/codex-pv-relink-20261028
export PATH=/home/dombarker/.cargo/bin:$PATH
cd "$d/native"
rustc +nightly-2026-06-01 -vV
cargo +nightly-2026-06-01 build --offline --release -j 4 --bin "$row"
"$d/native/target/release/$row"
sha256sum "$d/native/$row.rs" "$d/native/target/release/$row"
