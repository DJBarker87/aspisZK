#!/bin/bash
# X1b batch 2, INSIDE one fv_slot.sh scope: tests of the five crates' configurations on the final tree rw-E; SBF
# builds C2 (item C tree, both configurations), K and E; replays; the emission of rw-E with the M flag, native probe
# and gates. Time is expected in test compilation (about 4 minutes per configuration) and the three SBF builds.
set -u
W=/home/dombarker/project-offloads/future-version-20261111; X=$W/x1b; cd $W
echo "== $(date -u +%T) tests"; bash $X/bin/fv_x1b_test.sh rw-E program program2 verifier statement core > $X/logs/test-E.log 2>&1; grep -E "^STEP|test result" $X/logs/test-E.log
echo "== $(date -u +%T) builds"
bash $X/bin/fv_x1b_build.sh rw-tree C2 both
bash $X/bin/fv_x1b_build.sh rw-K K aspis
bash $X/bin/fv_x1b_build.sh rw-E E both
echo "== $(date -u +%T) replays"
for n in K E; do bash $X/bin/fv_x1b_replay.sh $n $W/out/X1b-$n/artifacts/aspis_r1_cost_probe_program.so; done
echo "== $(date -u +%T) emission"; bash $X/bin/fv_x1b_job.sh E $X/bin/fv_x1b_cfg_E.json
echo "== $(date -u +%T) done"
