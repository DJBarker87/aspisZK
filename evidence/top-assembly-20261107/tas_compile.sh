#!/bin/sh
# Focused single-file compile of TCK_WeakRoot0, TAS_Interfaces, TAS_Top against RSL_.
# Run from evidence/rowspec-lead-20261107 after its RSL modules are built (rsl_compile.sh).
# `lake env lean -o` requires the input under the package root, so files are staged
# into the ignored .lake/stage/ directory first; their sha256 is recorded.
set -u
mkdir -p .lake/stage .lake/build/lib/lean
cp ../top-check-20261107/TCK_WeakRoot0.lean ../top-assembly-20261107/TAS_Interfaces.lean \
   ../top-assembly-20261107/TAS_Top.lean .lake/stage/
for m in TCK_WeakRoot0 TAS_Interfaces TAS_Top; do
  out=$( { /usr/bin/time -l lake env lean -o ".lake/build/lib/lean/$m.olean" ".lake/stage/$m.lean" ; } 2>&1 )
  rc=$?
  printf '%s\texit=%s\t%s\n' "$m" "$rc" "$(shasum -a 256 .lake/stage/$m.lean | cut -d' ' -f1)"
  printf '%s\n' "$out" | grep -E 'depends on|error|maximum resident| real'
  [ $rc -ne 0 ] && exit $rc
done
exit 0
