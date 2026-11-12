#!/bin/bash
W=/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111; cd $W
bash tools/d_chain.sh r3 src-rw i3c-apply_mask_material i5c-sparse_eq_weights
bash tools/emit_fix3.sh i68-check_times_client > emit_fix3.log 2>&1
PV_KEEP_AXIOMS=1 bash tools/l_chain.sh r2 roots/lean-r2.txt
echo done > ROUND3.DONE
