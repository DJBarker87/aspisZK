#!/bin/bash
# W9 = W8 without the dropped E6; plain build on six fixtures, then a debug-line build and traces of it.
W=/home/dombarker/project-offloads/future-version-20261111
cd $W
F9=private-leaf-salts,future-fast-kmul,future-fast-prepared,future-fast-square,future-validated-decode,future-merkle-single-pass,future-tight-base,future-tight-weights,future-lazy-boundary
bash fv_scope.sh W9-keep 1800 bash $W/fv_build.sh W9-keep $F9 || { echo BUILD_FAILED > $W/ALL8_DONE; exit 1; }
for f in transfer-13 transfer-255 transfer-1023 withdrawal-13 withdrawal-255 withdrawal-1023; do bash fv_scope.sh M8-W9-keep-$f 300 bash $W/fv_run.sh W9-keep $f; done
bash fv_scope.sh W9-dbg 1800 bash $W/fv_build_dbg.sh W9-dbg $F9 || { echo DBG_BUILD_FAILED > $W/ALL8_DONE; exit 1; }
bash fv_scope.sh T2-W9-transfer-13-tag9 900 bash $W/fv_trace.sh W9-dbg transfer-13 9
echo done > $W/ALL8_DONE
