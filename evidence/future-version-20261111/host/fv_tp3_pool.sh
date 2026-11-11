#!/bin/bash
# Translatability pass, worker 3: Pool check for a changed tree. Builds the Pool with the deployed Pool recipe
# (fv_pool_build.sh, read-only use) from <tree>, compares the ELF with out/PL-base (built from the same Pool,
# core and statement sources as src-base2), and if it differs runs the Pool crate's tests (fv_pool_test.sh) and
# replays the recorded payments with the changed Pool ELF (fv_pool_replay.sh).
# Usage: fv_tp3_pool.sh <name> <tree>. Time: one SBF build; tests and replays only if the ELF changed.
W=/home/dombarker/project-offloads/future-version-20261111
cd $W
N=$1; S=$2
D=$W/TP3POOL_$N.done; rm -f $D
bash fv_slot.sh T3-PB-$N 3000 bash $W/fv_pool_build.sh T3-PL-$N $S || { echo POOL_BUILD_FAILED > $D; exit 1; }
B=$(awk '{print $1}' out/PL-base/so.sha256); C=$(awk '{print $1}' out/T3-PL-$N/so.sha256)
if [ "$B" = "$C" ]; then echo "POOL_ELF_UNCHANGED $C" > $D; exit 0; fi
echo "POOL_ELF_CHANGED base $B new $C" > $D
bash fv_pool_test.sh $S >> $D 2>&1
bash fv_pool_replay.sh tp3-$N $W/out/T3-PL-$N/artifacts/aspis_pool.so >> $D 2>&1
echo END >> $D
