#!/bin/bash
# Third round: the fast QM31 multiplication kernel everywhere (exact change). One scope at a time.
W=/home/dombarker/project-offloads/future-version-20261111
cd $W
bash fv_scope.sh B6-plain-fastk 1800 bash $W/fv_build.sh B6-plain-fastk private-leaf-salts,future-fast-kmul || { echo ELF_BUILD_FAILED > $W/ALL3_DONE; exit 1; }
bash fv_scope.sh B7-detail-fastk 1800 bash $W/fv_build.sh B7-detail-fastk private-leaf-salts,cu-profiling,detail-phases,future-fast-kmul || { echo ELF_BUILD_FAILED > $W/ALL3_DONE; exit 1; }
for f in transfer-13 withdrawal-255 transfer-255 transfer-1023 withdrawal-13 withdrawal-1023; do bash fv_scope.sh M3-B6-plain-fastk-$f 300 bash $W/fv_run.sh B6-plain-fastk $f; done
for f in transfer-13 withdrawal-255; do bash fv_scope.sh M3-B7-detail-fastk-$f 300 bash $W/fv_run.sh B7-detail-fastk $f; done
echo done > $W/ALL3_DONE
