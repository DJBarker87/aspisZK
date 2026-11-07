#!/bin/sh
# Focused single-file compile: lake env lean -o <olean> <file>; records exit, wall, peak RSS.
# Usage: ./rsl_compile.sh RSL_X.lean [...]   (dependency order)
set -u
mkdir -p .lake/build/lib/lean
for f in "$@"; do
  m=$(basename "$f" .lean)
  out=$( { /usr/bin/time -l lake env lean -o ".lake/build/lib/lean/$m.olean" "$f" ; } 2>&1 )
  rc=$?
  wall=$(printf '%s\n' "$out" | awk '/ real /{print $1}')
  rss=$(printf '%s\n' "$out" | awk '/maximum resident set size/{print $1}')
  swaps=$(printf '%s\n' "$out" | awk '/ swaps$/{print $1}')
  printf '%s\texit=%s\twall_s=%s\tpeak_rss_bytes=%s\tswaps=%s\n' "$f" "$rc" "$wall" "$rss" "$swaps" | tee -a RSL_COMPILE_LOG.tsv
  printf '%s\n' "$out" | grep -v '^ *[0-9]\+  [a-z]' | grep -v ' real ' | head -60
  [ $rc -ne 0 ] && exit $rc
done
exit 0
