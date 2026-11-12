#!/bin/bash
# X6 focused compile of candidate files, one at a time, against the dependency objects already built.
# Runs INSIDE one fv_slot.sh scope:  bash W/fv_slot.sh X6-try-<n> <timeout> bash W/x6/bin/fv_x6_try.sh <tc> <outdir> <Module>=<file> ...
#   <tc> new: Lean 4.36.0-rc2, LEAN_PATH W/x6/objs + stage A library (as fv_x6_compile.sh)
#   <tc> old: Lean 4.32.0, LEAN_PATH = X3's coherent 4.32 carried set, read only:
#             W/x3/map4-old/out : W/x3/l187-carried4 : L187 base_ref (packages only)
# Objects of the candidate go to <outdir>/obj (never to W/x6/objs); log and time per file in <outdir>.
set -u
W=/home/dombarker/project-offloads/future-version-20261111
Y=$W/x6; B=$W/x3/aeneas-src/backends/lean; L=/home/dombarker/project-offloads/codex-cx-replay-l187-20261109
tc=$1; O=$2; shift 2
mkdir -p $O/obj
if [ "$tc" = new ]; then
  TCD=$HOME/.elan/toolchains/leanprover--lean4---v4.36.0-rc2
  LP=$Y/objs:$B/.lake/build/lib/lean; for p in $B/.lake/packages/*; do LP=$LP:$p/.lake/build/lib/lean; done
else
  TCD=$HOME/.elan/toolchains/leanprover--lean4---v4.32.0
  LP=$W/x3/map4-old/out:$W/x3/l187-carried4:$L/base_ref
fi
for a in "$@"; do
  m=${a%%=*}; f=${a#*=}; rel=${m//.//}; mkdir -p $O/obj/$(dirname $rel)
  s=$(date +%s.%N)
  /usr/bin/time -v -o $O/$m.$tc.time env PATH=/usr/bin:/bin LEAN_PATH=$LP timeout 900 $TCD/bin/lean -j1 -M7000 \
    -DElab.async=false -o $O/obj/$rel.olean $f > $O/$m.$tc.log 2>&1
  rc=$?; e=$(date +%s.%N)
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$m" "$tc" "$rc" "$(python3 -c "print(round($e-$s,2))")" \
    "$(grep 'Maximum resident' $O/$m.$tc.time | awk '{print $NF}')" "$(grep -c ': error' $O/$m.$tc.log)" >> $O/result.tsv
done
echo done > $O/DONE
