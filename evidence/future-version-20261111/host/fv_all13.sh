#!/bin/bash
# One transaction through the Pool: adapter build with the kept feature set and future-one-tx, replay driver,
# then the recorded devnet transfer and withdrawal settlements.
W=/home/dombarker/project-offloads/future-version-20261111
cd $W
FK=pool-adapter,private-leaf-salts,future-one-tx,future-fast-kmul,future-fast-prepared,future-fast-square,future-validated-decode,future-merkle-single-pass,future-tight-base,future-tight-weights,future-lazy-boundary,future-d-inactive-tensor,future-d-pair-expansion,future-merkle-in-place,future-lazy-horner,future-fold-shared
bash fv_scope.sh A1-onetx 1800 bash $W/fv_build_adapter.sh A1-onetx $FK || { echo ADAPTER_BUILD_FAILED > $W/ALL13_DONE; exit 1; }
bash fv_scope.sh D7-driver 3000 bash $W/fv_driver_build.sh || { echo DRIVER_BUILD_FAILED > $W/ALL13_DONE; exit 1; }
bash fv_scope.sh R1-A1-onetx-transfer 600 bash $W/fv_replay.sh A1-onetx transfer
bash fv_scope.sh R1-A1-onetx-withdrawal 600 bash $W/fv_replay.sh A1-onetx withdrawal
echo done > $W/ALL13_DONE
