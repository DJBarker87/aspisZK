#!/bin/bash
# Second round: detail build with the unit-cost and relation probes; rebuilt driver. One scope at a time.
W=/home/dombarker/project-offloads/future-version-20261111
cd $W
bash fv_scope.sh B4-detail2 1800 bash $W/fv_build.sh B4-detail2 private-leaf-salts,cu-profiling,detail-phases || { echo ELF_BUILD_FAILED > $W/ALL2_DONE; exit 1; }
bash fv_scope.sh B5-plain2 1800 bash $W/fv_build.sh B5-plain2 private-leaf-salts || { echo ELF_BUILD_FAILED > $W/ALL2_DONE; exit 1; }
bash fv_scope.sh D2-driver 3000 bash $W/fv_driver_build.sh || { echo DRIVER_BUILD_FAILED > $W/ALL2_DONE; exit 1; }
for f in transfer-13 withdrawal-255; do
  for e in B4-detail2 B5-plain2; do bash fv_scope.sh M2-$e-$f 300 bash $W/fv_run.sh $e $f; done
done
echo done > $W/ALL2_DONE
