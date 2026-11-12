#!/bin/bash
# Second version of fv_tp1_gate1.sh (see fv_tp1_gate2_inner.sh for the one difference: the program crate's tests).
# Aspis translatability pass: everything one batch must pass, in ONE fv_slot.sh scope (8 GiB cap), so that the
# batch waits for a host slot once and not once per step. The steps are those of fv_tp1_batch.sh and fv_tp1_gate.sh
# (that is, of the shared gate fv_sampler_gate.sh and of fv_round7.sh, command for command), run one after another by
# fv_tp1_gate2_inner.sh; the files written have the names and layout fv_gate_compare.py reads.
# Usage: fv_tp1_gate2.sh <name> <tree> <base-tree> <label>=<base ELF> <label>
# Time is expected in compilation (five target directories of the changed tree: unit tests, client configuration,
# SBF program, mutant tool, worst-case tool), then about twenty seconds per mutant campaign and a minute of worst-case runs.
W=/home/dombarker/project-offloads/future-version-20261111
cd $W
N=$1; S=$2; H=$3; HEADELF=$4; LABEL=$5
rm -f $W/GATE_$N.done $W/MUTANTS_g-$N.done $W/ROUND7_$N.done
bash fv_slot.sh TP-G-$N 6000 bash $W/fv_tp1_gate2_inner.sh $N $S $H $HEADELF > $W/tp1/gate2-$N.log 2>&1
echo "scope exit $?"
cat $W/tp1/gate2-$N.steps 2>/dev/null
python3 fv_gate_compare.py $N $LABEL 2>&1 | cut -c1-400; echo "gate compare exit ${PIPESTATUS[0]}"
