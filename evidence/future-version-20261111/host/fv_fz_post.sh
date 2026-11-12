#!/bin/bash
# Naming cleanup (fz): read-only comparisons after the gate. Usage: fv_fz_post.sh <name> <tree>
W=/home/dombarker/project-offloads/future-version-20261111
cd $W
N=$1; S=$2
BU=$W/tp1/gate2-cand1/unstripped-src-cand1.so; NU=$W/fz/gate-$N/unstripped-$S.so
BE=$W/out/cand1/artifacts/aspis_r1_cost_probe_program.so; NE=$W/out/$N/artifacts/aspis_r1_cost_probe_program.so
echo "## sha256 and size"; sha256sum $BE $NE $BU $NU; stat -c '%s %n' $BE $NE $BU $NU
echo "## stripped ELFs byte-identical: $(cmp -s $BE $NE && echo yes || echo no)"
echo "## unstripped ELFs byte-identical: $(cmp -s $BU $NU && echo yes || echo no)"
echo "## fv_tp1_symcmp2.sh (names and sizes, unmapped)"; bash $W/fv_tp1_symcmp2.sh $BU $NU
echo "## fv_fz_fnbytes.py (masked bytes, control names through the rename map)"; python3 $W/fv_fz_fnbytes.py $BU $NU $W/fv_fz_rename_map.tsv; echo "fnbytes exit $?"
