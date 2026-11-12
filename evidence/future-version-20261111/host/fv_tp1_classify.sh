#!/bin/bash
# Aspis translatability pass, verifier crate and program adapter: the classification runs at the head (src-xp1).
# Each step is one fv_slot.sh scope, one at a time. Usage: fv_tp1_classify.sh   (from the workspace)
# Time is expected in Charon's cargo build (cold target directory per tree and tool pair), then about a minute per Aeneas run.
W=/home/dombarker/project-offloads/future-version-20261111
cd $W/tp1 || exit 1
L=$W/tp1/classify.log; : > $L
run() { bash $W/fv_slot.sh "$@" >> $L 2>&1; echo "$1 exit $?" >> $L; }
run TP-C02 1200 python3 TP_charon.py TP-C02.json
test -f runs/TP-C02/out.llbc && run TP-A02 400 python3 TP_aeneas.py TP-C02 TP-A02 second AspisTPp noabort
run TP-C03 1200 python3 TP_charon.py TP-C03.json
test -f runs/TP-C03/out.llbc && run TP-A03 400 python3 TP_aeneas.py TP-C03 TP-A03 first AspisTPq noabort
run TP-C04 1200 python3 TP_charon.py TP-C04.json
test -f runs/TP-C04/out.llbc && run TP-A04 400 python3 TP_aeneas.py TP-C04 TP-A04 first AspisTPr noabort
echo DONE >> $L
