#!/bin/sh
# Focused single-file compile of MAT_MultiAttempt against RSL_ + TCK_ + TAS_ + TFM_ + EVB_ + TAS_TopB oleans.
# Run from evidence/rowspec-lead-20261107 after rsl_compile.sh (RSL_Base .. RSL_TX1_330) and
# staged compiles of TCK_WeakRoot0, TAS_Interfaces, TAS_Top, TFM_TopExact, EVB_EventB, TAS_TopB
# (lake env lean -o .lake/build/lib/lean/<m>.olean .lake/stage/<m>.lean, in that order).
set -u
mkdir -p .lake/stage .lake/build/lib/lean
cp ../multi-attempt-20261108/MAT_MultiAttempt.lean .lake/stage/
m=MAT_MultiAttempt
out=$( { /usr/bin/time -l lake env lean -o ".lake/build/lib/lean/$m.olean" ".lake/stage/$m.lean" ; } 2>&1 )
rc=$?
wall=$(printf '%s\n' "$out" | awk '/ real /{print $1}')
rss=$(printf '%s\n' "$out" | awk '/maximum resident set size/{print $1}')
swaps=$(printf '%s\n' "$out" | awk '/ swaps$/{print $1}')
printf 'file\texit\twall_s\tpeak_rss_bytes\tswaps\tsha256\trevision_base\n%s.lean\texit=%s\twall_s=%s\tpeak_rss_bytes=%s\tswaps=%s\tsha256=%s\t%s\n' \
  "$m" "$rc" "$wall" "$rss" "$swaps" "$(shasum -a 256 .lake/stage/$m.lean | cut -d' ' -f1)" "$(git rev-parse --short HEAD)" > ../multi-attempt-20261108/MAT_COMPILE.tsv
printf '%s\n' "$out" | grep -v 'maximum resident\|^ *[0-9]\+  [a-z]\| real ' > ../multi-attempt-20261108/MAT_AXIOMS_OUTPUT.txt
cat ../multi-attempt-20261108/MAT_COMPILE.tsv ../multi-attempt-20261108/MAT_AXIOMS_OUTPUT.txt
exit $rc
