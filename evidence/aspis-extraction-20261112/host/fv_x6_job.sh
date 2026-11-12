#!/bin/bash
# X6 slot job: optional diagnostics, then the compile table of the ported tree, then the resumed compile pass.
# Order: diagnostics, table, compile pass, optional 4.32 test of patched modules.
# Runs INSIDE one fv_slot.sh scope:  bash W/fv_slot.sh X6-<name> <timeout> bash W/x6/bin/fv_x6_job.sh <tag> [diag files...]
#   <tag>: names the diagnostic output directory W/x6/diag-out/<tag>
#   diag files: <Module>=<path> pairs passed to fv_x6_try.sh new (objects never go to W/x6/objs)
# Diagnostics may use options that are not allowed in a port patch (debug.skipKernelTC, only to print an
# elaborated proof term); such a file is never part of the ported tree.
set -u
Y=/home/dombarker/project-offloads/future-version-20261111/x6
tag=$1; shift
if [ $# -gt 0 ]; then bash $Y/bin/fv_x6_try.sh new $Y/diag-out/$tag "$@"; fi
python3 -I $Y/bin/fv_x6_table.py $Y/closure/carried-table.tsv $Y/ported-src $Y/closure/ported-table.tsv || exit 5
bash $Y/bin/fv_x6_compile.sh $Y/closure/ported-table.tsv $Y/run
# optional: Lean 4.32.0 test of the patched modules listed in W/x6/oldtest-<tag>.txt (<Module>=<path> per line),
# against X3's coherent 4.32 carried object set (fv_x6_try.sh old); results in W/x6/diag-out/<tag>-old
if [ -s $Y/oldtest-$tag.txt ]; then bash $Y/bin/fv_x6_try.sh old $Y/diag-out/$tag-old $(cat $Y/oldtest-$tag.txt); fi
