#!/bin/bash
W=/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111; cd $W
PV_KEEP_AXIOMS=1 bash tools/l_chain.sh r4 roots/lean-r4.txt
python3 tools/sorrydiag.py c2c-copy_registry && bash tools/lean_check.sh c2c-copy_registry-diag 1 > sorrydiag.log 2>&1
echo done > ROUND5.DONE
