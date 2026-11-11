#!/bin/bash
# Aspis extraction probe: run the existing unit tests that compare the changed kernels with their references, on one
# source directory (inside an fv_slot.sh scope). usage: XP_test.sh <src dir name> <run name>
set -u
E=/home/dombarker/project-offloads/future-version-20261111/extract-probe
export PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_NET_OFFLINE=true CARGO_BUILD_JOBS=4 CARGO_TARGET_DIR=$E/target/test
mkdir -p $E/runs/$2
cd $E/$1 && cargo +1.94.1 test --offline --locked --release -p aspis-r1-cost-probe --lib --features private-leaf-salts,aspis-core/future-fast-kmul,aspis-core/future-fast-prepared,aspis-core/future-fast-square,aspis-core/future-lazy-horner,future-validated-decode,future-merkle-single-pass,future-tight-base,future-tight-weights,future-lazy-boundary,future-d-inactive-tensor,future-d-pair-expansion,future-merkle-in-place,future-fold-shared -- stage_d summed_format merged_slot rho_dependent batched_sums tight_lane validated_decode boundary_sum all_three_verifiers single_pass > $E/runs/$2/test.log 2>&1
rc=$?; grep -E "^test |test result|^error" $E/runs/$2/test.log | cut -c1-200 | tail -40; exit $rc
