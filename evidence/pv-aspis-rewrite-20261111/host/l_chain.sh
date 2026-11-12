#!/bin/bash
# Gate D, Lean side: for each "CHECKTAG EMISSIONTAG TARGET..." line of the given file, build the check file
# from that emission (mkcheck.py) and compile it in its own scope (lean_check.sh). usage: l_chain.sh NAME FILE
W=/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111
N=$1; cd $W
while read ct et targets; do
  [ -n "$ct" ] || continue
  [ -e emit/$ct ] || ln -s $W/emit/$et emit/$ct
  PV_KEEP_AXIOMS=${PV_KEEP_AXIOMS:-0} python3 tools/mkcheck.py $ct $targets > check-$ct.mk.log 2>&1 || { echo "$ct MKCHECK_FAILED" >> l_chain_$N.log; continue; }
  bash tools/lean_check.sh $ct 1 >> l_chain_$N.log 2>&1
done < $2
echo done > $W/L_CHAIN_$N.DONE
