#!/usr/bin/env bash
set -euo pipefail
H=/home/dombarker/project-offloads/codex-cx-asq8-kani-20261021
export PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin
export CARGO_TARGET_DIR=$H/kani-target CARGO_BUILD_JOBS=4
[[ $(cargo kani --version) == 'cargo-kani 0.67.0' ]]
for target in transfer_encoder_equivalence withdrawal_encoder_equivalence accepted_request_reencodes_exactly request_decoder_equivalence; do
    python3 "$H/harness/reservation.py" "$H/reservation-kani-v4-$target.json" >/dev/null
    "$H/harness/capped-run.sh" "kani-v4-$target" \
        "Final reference: Kani compilation and symbolic $target; 320 byte output, no arithmetic elimination" \
        "$H/src" -- cargo kani -p aspis-statement --lib --exact \
        --harness "pool_v1::pair_forest_terminal::asq8_kani::$target" \
        --no-assertion-reach-checks --solver kissat --output-format old \
        -Z unstable-options --cbmc-args --unwinding-assertions
done
