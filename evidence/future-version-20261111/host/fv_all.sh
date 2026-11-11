#!/bin/bash
# Detached driver: three SBF variants, the host driver, then the measurements. One scope at a time.
W=/home/dombarker/project-offloads/future-version-20261111
cd $W
bash fv_scope.sh B1-plain 1800 bash $W/fv_build.sh B1-plain private-leaf-salts
bash fv_scope.sh B2-profile 1800 bash $W/fv_build.sh B2-profile private-leaf-salts,cu-profiling
bash fv_scope.sh B3-detail 1800 bash $W/fv_build.sh B3-detail private-leaf-salts,cu-profiling,detail-phases
bash fv_scope.sh D1-driver 3000 bash $W/fv_driver_build.sh || { echo DRIVER_BUILD_FAILED > $W/ALL_DONE; exit 1; }
for f in transfer-13 withdrawal-255; do
  for e in B1-plain B2-profile B3-detail; do bash fv_scope.sh M-$e-$f 300 bash $W/fv_run.sh $e $f; done
done
for f in transfer-255 transfer-1023 withdrawal-13 withdrawal-1023; do bash fv_scope.sh M-B1-plain-$f 300 bash $W/fv_run.sh B1-plain $f; done
echo done > $W/ALL_DONE
