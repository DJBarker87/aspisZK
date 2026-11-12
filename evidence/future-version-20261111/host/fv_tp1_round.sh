#!/bin/bash
# Aspis translatability pass: one round of checks on a candidate tree in ONE fv_slot.sh scope (8 GiB cap), so that the
# round waits for a host slot once: a construct probe (optional), the compute of the candidate and of its variants
# (fv_tp1_bisect_inner.sh), then the translation and Lean elaboration of the candidate (fv_tp1_emit1_inner.sh).
# Usage: fv_tp1_round.sh <round> <probe or -> <bisect-tag> "<variants>" <emit-tag> <verifier-spec> <program-spec>
W=/home/dombarker/project-offloads/future-version-20261111
cd $W
R=$1; MINI=$2; BT=$3; VARS=$4; ET=$5; CV=$6; CP=$7
[ "$MINI" = "-" ] && MINI=
bash fv_slot.sh TP-R-$R 7200 bash -c "MINI=$MINI bash $W/fv_tp1_bisect_inner.sh $BT $VARS; bash $W/fv_tp1_emit1_inner.sh $ET $CV $CP" > $W/tp1/round-$R.log 2>&1
echo "scope exit $?"; cat $W/tp1/bisect-$BT.txt 2>/dev/null | cut -c1-220; cat $W/tp1/emit1-$ET.steps 2>/dev/null | cut -c1-260
