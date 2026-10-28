#!/bin/sh
set -eu
cd /home/dombarker/project-offloads/codex-pv-fxmem-20261028
rustc +nightly-2026-06-01 --version --verbose
rustc +nightly-2026-06-01 -O -C panic=unwind drop-counterexample.rs -o drop-counterexample
./drop-counterexample
