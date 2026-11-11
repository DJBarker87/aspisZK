#!/bin/bash
# Round 2 inventory tooling: debug-line ELF of the W0 feature set and the trace driver.
W=/home/dombarker/project-offloads/future-version-20261111
cd $W
bash fv_scope.sh B8-w0-dbg 1800 bash $W/fv_build_dbg.sh B8-w0-dbg private-leaf-salts,future-fast-kmul || { echo ELF_BUILD_FAILED > $W/ALL4_DONE; exit 1; }
bash fv_scope.sh D3-trace 3000 bash $W/fv_trace_build.sh || { echo TRACE_BUILD_FAILED > $W/ALL4_DONE; exit 1; }
echo done > $W/ALL4_DONE
