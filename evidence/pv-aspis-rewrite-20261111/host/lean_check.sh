#!/bin/bash
# usage: lean_check.sh TAG [RUN]   One capped scope: lake env lean on check/TAG/RwCheck.lean against the compiled
# objects of package g2 (read in place) and the Aeneas/Mathlib seed of the earlier jobs (by reference).
# Same Lean (4.32.0) and flags as pv-combined-20261111 tools/lean_one.sh. Nothing of the package is rebuilt.
W=/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111
T=/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0
export PATH=$T/bin:/usr/bin:/bin LEAN_SYSROOT=$T PV_SRC_REV=$(cat $W/SOURCE_REVISION)
tag=$1; run=${2:-1}; root=$W/check/$tag; obj=$root/objs; mkdir -p $obj
export LEAN_PATH=$obj:/home/dombarker/project-offloads/codex-pv-combined-20261111/objs/g2:/home/dombarker/project-offloads/codex-pv-replay-20261027/objects
mkdir -p $W/lean; cd $W/lean
[ -e lean-toolchain ] || echo "leanprover/lean4:v4.32.0" > lean-toolchain
[ -e lakefile.toml ] || printf 'name = "pvrw"\nversion = "0.1.0"\n' > lakefile.toml
python3 $W/tools/run_job.py L-$tag-$run "lake env lean, one file check/$tag/RwCheck.lean against package g2 objects; time expected in elaboration of that file" 1800 $W/lean -- $T/bin/lake env lean -j1 -M7000 -DElab.async=false -DmaxErrors=100000 -R $root -o $obj/RwCheck.olean $root/RwCheck.lean > $W/runs/L-$tag-$run.driver.log 2>&1
tail -1 $W/runs/L-$tag-$run.driver.log
grep -c "error" $W/runs/L-$tag-$run/stdout.log
