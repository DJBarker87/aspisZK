#!/bin/bash
# usage: bash runl.sh <target-without-.lean>   (one Lean scope; next PCUH_Lnnn id)
cd /Users/dominic/ZK/.worktrees/pc-prov-p2h/evidence/prov-p2h-20261109
n=$(ls -d PCUH_L[0-9][0-9][0-9] 2>/dev/null | sed "s/PCUH_L//" | sort -n | tail -1 | sed "s/^0*//")
id=$(printf "PCUH_L%03d" $(( ${n:-0} + 1 )))
python3 PCUH_run.py $id lean $1 > run_$id.out 2>&1
echo "$id $1 exit=$?" | tee -a batch_summary.txt
