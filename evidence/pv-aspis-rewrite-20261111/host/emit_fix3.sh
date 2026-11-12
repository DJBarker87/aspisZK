#!/bin/bash
# Extra emission, not gate D: the translator that produced the base emission of package g2 (aeneas-pvfix3,
# sha256 edeb79b1...) on an LLBC of this job, to see what the tool of that emission does with functions that take the
# hash function pointer. usage: emit_fix3.sh TAG
W=/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111
F=/home/dombarker/project-offloads/codex-pv-extract-fix-20261111/toolsrc/bin/aeneas-pvfix3
tag=$1; cd $W
[ "$(sha256sum < $F | cut -d' ' -f1)" = edeb79b17c2a25397c2aff6a7c5aed5058300e841ef3a2d19ecf1fff84950813 ] || { echo FIX3-HASH-MISMATCH; exit 3; }
export PV_SRC_REV=$(cat $W/SOURCE_REVISION)
mkdir -p emit/$tag-fix3; ln -s $W/llbc/$tag.llbc emit/$tag-fix3/ProverPin2.llbc
python3 $W/tools/run_job.py AF-$tag "aeneas-pvfix3 (edeb79b1) on llbc/$tag.llbc, no -abort-on-error; time expected in symbolic execution and Lean emission" 900 $W/emit/$tag-fix3 -- $F -sequential -no-progress-bar -backend lean -namespace ProverPin2 -dest generated -split-files ProverPin2.llbc > $W/runs/AF-$tag.driver.log 2>&1
tail -1 $W/runs/AF-$tag.driver.log
