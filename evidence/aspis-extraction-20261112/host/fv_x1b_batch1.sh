#!/bin/bash
# X1b batch 1, INSIDE one fv_slot.sh scope: SBF builds of the frozen copy (both configurations) and of the item
# snapshots C, D (both configurations), J, F, L; the two recorded-payment replays for each; the item M depth test;
# the item E reproducer emission. Time is expected in the seven cold SBF compilations (about 3 minutes each).
set -u
W=/home/dombarker/project-offloads/future-version-20261111; X=$W/x1b; cd $W
echo "== $(date -u +%T) builds"
test -e $X/rw-0 || (mkdir -p $X/rw-0 && cd $W/src-frz-a && tar cf - --exclude=./target . | (cd $X/rw-0 && tar xf -))
bash $X/bin/fv_x1b_build.sh rw-0 0 both
bash $X/bin/fv_x1b_build.sh rw-tree C1 aspis
bash $X/bin/fv_x1b_build.sh rw-D D both
for n in J F L; do bash $X/bin/fv_x1b_build.sh rw-$n $n aspis; done
echo "== $(date -u +%T) replays"
for n in 0 C1 D J F L; do bash $X/bin/fv_x1b_replay.sh $n $W/out/X1b-$n/artifacts/aspis_r1_cost_probe_program.so; done
echo "== $(date -u +%T) recdepth"
bash $X/bin/fv_x1b_recdepth.sh $X/runs/C/runs/A-release/raw/AspisX1/Funs.lean $X/probe/recdepth 2048 4096 8192 16384
echo "== $(date -u +%T) probe-e"
(cd $X/probe/crate-e && env PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_NET_OFFLINE=true RUSTUP_TOOLCHAIN=nightly-2026-09-17 cargo generate-lockfile --offline > $X/logs/probe-e-lock.log 2>&1; echo "lock exit $?")
bash $X/bin/fv_x1b_job.sh probe-e $X/bin/fv_x1b_cfg_probe_e.json noabort
echo "== $(date -u +%T) done"
