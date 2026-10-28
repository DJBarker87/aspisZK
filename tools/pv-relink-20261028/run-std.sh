#!/bin/sh
set -eu
row="$1"
d=/home/dombarker/project-offloads/codex-pv-relink-20261028
rust=/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu/bin/rustc
"$rust" -vV
"$rust" --edition 2021 -O "$d/$row.rs" -o "$d/$row-native"
"$d/$row-native"
sha256sum "$d/$row.rs" "$d/$row-native"
