#!/bin/sh
# Focused single-file compile of TFM_TopExact against RSL_ + TCK_ + TAS_ oleans.
# Run from evidence/rowspec-lead-20261107 after rsl_compile.sh and
# ../top-assembly-20261107/tas_compile.sh.  Staged under the ignored .lake/stage/.
set -u
mkdir -p .lake/stage .lake/build/lib/lean
cp ../top-form-20261107/TFM_TopExact.lean .lake/stage/
m=TFM_TopExact
out=$( { /usr/bin/time -l lake env lean -o ".lake/build/lib/lean/$m.olean" ".lake/stage/$m.lean" ; } 2>&1 )
rc=$?
wall=$(printf '%s\n' "$out" | awk '/ real /{print $1}')
rss=$(printf '%s\n' "$out" | awk '/maximum resident set size/{print $1}')
swaps=$(printf '%s\n' "$out" | awk '/ swaps$/{print $1}')
printf 'file\texit\twall_s\tpeak_rss_bytes\tswaps\tsha256\n%s.lean\texit=%s\twall_s=%s\tpeak_rss_bytes=%s\tswaps=%s\tsha256=%s\n' \
  "$m" "$rc" "$wall" "$rss" "$swaps" "$(shasum -a 256 .lake/stage/$m.lean | cut -d' ' -f1)" > ../top-form-20261107/TFM_COMPILE.tsv
printf '%s\n' "$out" | grep -v 'maximum resident\|^ *[0-9]\+  [a-z]\| real ' > ../top-form-20261107/TFM_AXIOMS_OUTPUT.txt
cat ../top-form-20261107/TFM_COMPILE.tsv ../top-form-20261107/TFM_AXIOMS_OUTPUT.txt
exit $rc
