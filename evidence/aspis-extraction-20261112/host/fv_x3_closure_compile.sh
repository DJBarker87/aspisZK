#!/bin/bash
# X3 stage C: compile the import closure of AspisFailureBoundModel (W/x3/closure/closure-modules.tsv, dependency
# order) under the native toolchain, without editing any file. A module whose closure imports did not all compile
# is skipped. Per-module log, exit, wall and peak RSS in W/x3/closure/compile/.
# NOT RUN on 2026-11-12 (stage A not built). Runs INSIDE one fv_slot.sh scope:
#   bash W/fv_slot.sh X3-C-closure 21600 bash W/x3/bin/fv_x3_closure_compile.sh
# Sources are read in place (chain-src, the L187 src tree, the CompPoly checkout); only objects are written, under
# W/x3/closure/compile/out. Review point: if ten minutes pass without a new object, stop the job.
set -u
W=/home/dombarker/project-offloads/future-version-20261111
B=$W/x3/aeneas-src/backends/lean
TCD=$HOME/.elan/toolchains/leanprover--lean4---v4.36.0-rc2
C=$W/x3/closure; O=$C/compile; mkdir -p $O/out $O/log
LP=$O/out:$B/.lake/build/lib/lean
for p in $B/.lake/packages/*; do LP=$LP:$p/.lake/build/lib/lean; done
mkdir -p $O/ok
: > $O/result.tsv
tail -n +2 $C/closure-modules.tsv | while IFS=$'\t' read -r m kind tier src path lines sha ai am rd imps reason; do
  skip=""
  for i in ${imps//,/ }; do [ -f $O/ok/$i ] || { skip=$i; break; }; done
  if [ -n "$skip" ]; then printf '%s\tskipped\t\t\t\t%s\n' "$m" "$skip" >> $O/result.tsv; continue; fi
  rel=${m//.//}; mkdir -p $O/out/$(dirname $rel) $O/ok
  # -R: the root of the module's own source tree (path minus the module's relative path)
  root=${path%/$rel.lean}
  s=$(date +%s.%N)
  /usr/bin/time -v -o $O/log/$m.time env PATH=/usr/bin:/bin LEAN_PATH=$LP timeout 900 $TCD/bin/lean -j1 -M7000 \
    -DElab.async=false -R $root -o $O/out/$rel.olean $path > $O/log/$m.log 2>&1
  rc=$?; e=$(date +%s.%N)
  rss=$(grep "Maximum resident" $O/log/$m.time | awk '{print $NF}')
  nerr=$(grep -c ": error" $O/log/$m.log)
  first=$(grep -m1 ": error" $O/log/$m.log | cut -c1-300)
  [ $rc -eq 0 ] && touch $O/ok/$m
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$m" "$rc" "$(echo "$e - $s" | bc)" "$rss" "$nerr" "$first" >> $O/result.tsv
done
