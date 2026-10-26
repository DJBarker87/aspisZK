#!/bin/sh
# One named harness per capped launch. Symbolic verification is the expected
# cost; the copied Rust helper is tiny. Cargo dev profile is explicitly opt3.
set -eu
cd /home/dombarker/project-offloads/codex-pv-runjoin-20261026/effect-cuts
export PATH="$HOME/.cargo/bin:$PATH"
export CARGO_BUILD_JOBS=4
export CARGO_PROFILE_DEV_OPT_LEVEL=3
attempt=$1
harness=$2
python3 ../reservation-existing.py ../evidence/kani-effect-$attempt-inside.json --requested-bytes 0
/usr/bin/time -v -o ../evidence/kani-effect-$attempt.time timeout 180 cargo kani --lib -j 4 --output-format terse --harness "$harness" --exact --verbose > ../evidence/kani-effect-$attempt.log 2>&1
