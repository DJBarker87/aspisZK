#!/bin/bash
# Trace of W13 (summed path, tag 13): rebuild drivers (certificate file, third-account prefix), a plain run to
# produce the certificate, a debug-line build of the W13 feature set, and the trace.
W=/home/dombarker/project-offloads/future-version-20261111
cd $W
F13=private-leaf-salts,future-fast-kmul,future-fast-prepared,future-fast-square,future-validated-decode,future-merkle-single-pass,future-tight-base,future-tight-weights,future-lazy-boundary,future-d-inactive-tensor,future-d-pair-expansion,future-merkle-in-place
bash fv_scope.sh D5-driver 3000 bash $W/fv_driver_build.sh || { echo DRIVER_BUILD_FAILED > $W/ALL11_DONE; exit 1; }
bash fv_scope.sh D6-trace 3000 bash $W/fv_trace_build.sh || { echo TRACE_BUILD_FAILED > $W/ALL11_DONE; exit 1; }
bash fv_scope.sh W13-dbg 1800 bash $W/fv_build_dbg.sh W13-dbg $F13 || { echo DBG_BUILD_FAILED > $W/ALL11_DONE; exit 1; }
bash fv_scope.sh M11-W13-dbg-transfer-13 300 bash $W/fv_run.sh W13-dbg transfer-13
bash fv_scope.sh T3-W13-transfer-13-tag13 900 bash $W/fv_trace.sh W13-dbg transfer-13 13 $W/measurements/W13-dbg-transfer-13.cert
echo done > $W/ALL11_DONE
