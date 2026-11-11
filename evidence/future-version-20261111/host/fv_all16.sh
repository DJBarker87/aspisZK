#!/bin/bash
# Round 5, second pass: adapter build with the wrapper fix, rebuilt replay tool, the two devnet settlements.
W=/home/dombarker/project-offloads/future-version-20261111
cd $W
K=private-leaf-salts,future-fast-kmul,future-fast-prepared,future-fast-square,future-validated-decode,future-merkle-single-pass,future-tight-base,future-tight-weights,future-lazy-boundary,future-d-inactive-tensor,future-d-pair-expansion,future-merkle-in-place,future-lazy-horner,future-fold-shared
bash fv_scope.sh A4-onetx-summed 1800 bash $W/fv_build_adapter.sh A4-onetx-summed pool-adapter,future-one-tx,$K || { echo ADAPTER_BUILD_FAILED > $W/ALL16_DONE; exit 1; }
bash fv_scope.sh D9-driver 3000 bash $W/fv_driver_build.sh || { echo DRIVER_BUILD_FAILED > $W/ALL16_DONE; exit 1; }
bash fv_scope.sh R4-A4-onetx-summed-transfer 600 bash $W/fv_replay.sh A4-onetx-summed transfer
bash fv_scope.sh R4-A4-onetx-summed-withdrawal 600 bash $W/fv_replay.sh A4-onetx-summed withdrawal
echo done > $W/ALL16_DONE
