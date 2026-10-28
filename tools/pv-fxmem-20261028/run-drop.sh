#!/bin/sh
set -eu
cd /home/dombarker/project-offloads/codex-pv-fxmem-20261028
pinned_rustc=/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu/bin/rustc
"$pinned_rustc" --version --verbose
"$pinned_rustc" -O -C panic=unwind drop-counterexample.rs -o drop-counterexample
./drop-counterexample
