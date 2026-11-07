#!/bin/sh
# Focused single-file compile of EVB_EventB against RSL_ + TCK_ + TAS_ + TFM_ oleans.
# Run from evidence/rowspec-lead-20261107 after rsl_compile.sh,
# ../top-assembly-20261107/tas_compile.sh and ../top-form-20261107/tfm_compile.sh.
set -u
mkdir -p .lake/stage .lake/build/lib/lean
cp ../event-b-20261107/EVB_EventB.lean .lake/stage/
m=EVB_EventB
out=$( { /usr/bin/time -l lake env lean -o ".lake/build/lib/lean/$m.olean" ".lake/stage/$m.lean" ; } 2>&1 )
rc=$?
wall=$(printf '%s\n' "$out" | awk '/ real /{print $1}')
rss=$(printf '%s\n' "$out" | awk '/maximum resident set size/{print $1}')
swaps=$(printf '%s\n' "$out" | awk '/ swaps$/{print $1}')
printf 'file\texit\twall_s\tpeak_rss_bytes\tswaps\tsha256\n%s.lean\texit=%s\twall_s=%s\tpeak_rss_bytes=%s\tswaps=%s\tsha256=%s\n' \
  "$m" "$rc" "$wall" "$rss" "$swaps" "$(shasum -a 256 .lake/stage/$m.lean | cut -d' ' -f1)" > ../event-b-20261107/EVB_COMPILE.tsv
printf '%s\n' "$out" | grep -v 'maximum resident\|^ *[0-9]\+  [a-z]\| real ' > ../event-b-20261107/EVB_AXIOMS_OUTPUT.txt
cat ../event-b-20261107/EVB_COMPILE.tsv ../event-b-20261107/EVB_AXIOMS_OUTPUT.txt
exit $rc
