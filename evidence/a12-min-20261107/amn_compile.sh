#!/bin/sh
# Focused single-file compiles of AMN_ReturnedPath and AMN_Minimal.
# Prerequisite: in a copy of evidence/rowspec-lead-20261107 (lakefile.toml, lean-toolchain
# v4.31.0), build the 20 RSL modules with rsl_compile.sh in the RSL_COMPILE_REV2.tsv order,
# then TCK_WeakRoot0 (git show research:evidence/top-check-20261107/TCK_WeakRoot0.lean) and
# TAS_Interfaces (evidence/top-assembly-20261107).  Then copy the AMN files there and run this.
set -u
mkdir -p .lake/build/lib/lean
for m in AMN_ReturnedPath AMN_Minimal; do
  out=$( { /usr/bin/time -l lake env lean -o ".lake/build/lib/lean/$m.olean" "$m.lean" ; } 2>&1 )
  rc=$?
  wall=$(printf '%s\n' "$out" | awk '/ real /{print $1}')
  rss=$(printf '%s\n' "$out" | awk '/maximum resident set size/{print $1}')
  swaps=$(printf '%s\n' "$out" | awk '/ swaps$/{print $1}')
  printf '%s.lean\texit=%s\twall_s=%s\tpeak_rss_bytes=%s\tswaps=%s\tsha256=%s\n' "$m" "$rc" "$wall" "$rss" "$swaps" "$(shasum -a 256 $m.lean | cut -d' ' -f1)"
  printf '%s\n' "$out" | grep -E "depends on|does not depend|error" >> AMN_AXIOMS_OUTPUT.txt
  [ $rc -ne 0 ] && exit $rc
done
exit 0
