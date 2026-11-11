#!/bin/bash
# Round 2 inventory: traces of W0 (batched, tag 9) and of the fused pinned mathematics (tag 8).
W=/home/dombarker/project-offloads/future-version-20261111
cd $W
bash fv_scope.sh T1-B8-transfer-13-tag9 900 bash $W/fv_trace.sh B8-w0-dbg transfer-13 9 || { echo TRACE_FAILED > $W/ALL5_DONE; exit 1; }
bash fv_scope.sh T1-B8-withdrawal-255-tag9 900 bash $W/fv_trace.sh B8-w0-dbg withdrawal-255 9
bash fv_scope.sh T1-B8-transfer-13-tag8 900 bash $W/fv_trace.sh B8-w0-dbg transfer-13 8
echo done > $W/ALL5_DONE
