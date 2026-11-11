#!/bin/bash
# Round 3, stage D: W10 = W9 feature set with the summed path (tag 13); rebuilt driver; plain build on six
# fixtures; profiled build on two.
W=/home/dombarker/project-offloads/future-version-20261111
cd $W
F9=private-leaf-salts,future-fast-kmul,future-fast-prepared,future-fast-square,future-validated-decode,future-merkle-single-pass,future-tight-base,future-tight-weights,future-lazy-boundary
bash fv_scope.sh W10-d 1800 bash $W/fv_build.sh W10-d $F9 || { echo BUILD_FAILED > $W/ALL9_DONE; exit 1; }
bash fv_scope.sh W10-d-profile 1800 bash $W/fv_build.sh W10-d-profile $F9,cu-profiling,detail-phases || { echo BUILD_FAILED > $W/ALL9_DONE; exit 1; }
bash fv_scope.sh D4-driver 3000 bash $W/fv_driver_build.sh || { echo DRIVER_BUILD_FAILED > $W/ALL9_DONE; exit 1; }
for f in transfer-13 transfer-255 transfer-1023 withdrawal-13 withdrawal-255 withdrawal-1023; do bash fv_scope.sh M9-W10-d-$f 300 bash $W/fv_run.sh W10-d $f; done
for f in transfer-13 withdrawal-255; do bash fv_scope.sh M9-W10-d-profile-$f 300 bash $W/fv_run.sh W10-d-profile $f; done
echo done > $W/ALL9_DONE
