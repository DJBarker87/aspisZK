#!/bin/sh
# Focused local compile of the NFB_ stand-in modules against the RSL_/TCK_/TAS_/TFM_/EVB_
# stand-in chain (core Lean only). Run from evidence/rowspec-lead-20261107 after
# rsl_compile.sh, ../top-assembly-20261107/tas_compile.sh, ../top-form-20261107/tfm_compile.sh,
# ../event-b-20261107/evb_compile.sh, and a compile of ../top-assembly-20261107/TAS_TopB.lean.
set -u
mkdir -p .lake/stage .lake/build/lib/lean
for m in NFB_BinderGroup NFB_NMFB; do
  cp ../nfb-20261108/$m.lean .lake/stage/
  out=$( { /usr/bin/time -l lake env lean -o ".lake/build/lib/lean/$m.olean" ".lake/stage/$m.lean" ; } 2>&1 )
  rc=$?
  printf '%s\texit=%s\tsha256=%s\n' "$m" "$rc" "$(shasum -a 256 .lake/stage/$m.lean | cut -d' ' -f1)"
  printf '%s\n' "$out" | grep -E 'depends on|error|maximum resident| real|swaps'
  [ $rc -ne 0 ] && exit $rc
done
exit 0
