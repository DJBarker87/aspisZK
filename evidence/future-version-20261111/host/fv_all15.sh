#!/bin/bash
# Round 5: W22 = the kept set with the summed-format path (tag 14), plain build on six fixtures and a
# profiled build on two; the one-transaction adapter build over the summed format replayed on the two
# recorded devnet settlements.
W=/home/dombarker/project-offloads/future-version-20261111
cd $W
K=private-leaf-salts,future-fast-kmul,future-fast-prepared,future-fast-square,future-validated-decode,future-merkle-single-pass,future-tight-base,future-tight-weights,future-lazy-boundary,future-d-inactive-tensor,future-d-pair-expansion,future-merkle-in-place,future-lazy-horner,future-fold-shared
bash fv_scope.sh W22-summed 1800 bash $W/fv_build.sh W22-summed $K || { echo BUILD_FAILED > $W/ALL15_DONE; exit 1; }
bash fv_scope.sh W22-summed-profile 1800 bash $W/fv_build.sh W22-summed-profile $K,cu-profiling,detail-phases || { echo BUILD_FAILED > $W/ALL15_DONE; exit 1; }
bash fv_scope.sh A3-onetx-summed 1800 bash $W/fv_build_adapter.sh A3-onetx-summed pool-adapter,future-one-tx,$K || { echo ADAPTER_BUILD_FAILED > $W/ALL15_DONE; exit 1; }
bash fv_scope.sh D8-driver 3000 bash $W/fv_driver_build.sh || { echo DRIVER_BUILD_FAILED > $W/ALL15_DONE; exit 1; }
for f in transfer-13 transfer-255 transfer-1023 withdrawal-13 withdrawal-255 withdrawal-1023; do bash fv_scope.sh M15-W22-summed-$f 300 bash $W/fv_run.sh W22-summed $f; done
for f in transfer-13 withdrawal-255; do bash fv_scope.sh M15-W22-summed-profile-$f 300 bash $W/fv_run.sh W22-summed-profile $f; done
bash fv_scope.sh R3-A3-onetx-summed-transfer 600 bash $W/fv_replay.sh A3-onetx-summed transfer
bash fv_scope.sh R3-A3-onetx-summed-withdrawal 600 bash $W/fv_replay.sh A3-onetx-summed withdrawal
echo done > $W/ALL15_DONE
