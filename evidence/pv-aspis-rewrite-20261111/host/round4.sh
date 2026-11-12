#!/bin/bash
W=/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111; cd $W
bash tools/d_chain.sh r4 src-rw i3d-apply_mask_material
PV_KEEP_AXIOMS=1 bash tools/l_chain.sh r3 roots/lean-r3.txt
echo done > ROUND4.DONE
