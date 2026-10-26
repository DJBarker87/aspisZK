#!/bin/sh
set -eu
cd /home/dombarker/project-offloads/codex-pv-runjoin-20261026/pv5-zeroize-kani
export PATH="$HOME/.cargo/bin:$PATH"
export CARGO_BUILD_JOBS=4
export CARGO_PROFILE_DEV_OPT_LEVEL=3
/usr/bin/time -v -o kani-01.time timeout 180 cargo kani --lib -j 4 --output-format terse --harness proofs::zeroizing_new_as_mut64_source_values --exact --verbose > kani-01.log 2>&1
