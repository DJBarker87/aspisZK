#!/bin/sh
# Focused single-file compile (one file at a time, core Lean only):
#   cp <path> .lake/stage/<module>.lean   (byte-identical staging copy; Lean 4.31
#     requires the input under --root, and sources live in several evidence dirs)
#   lake env lean --root=.lake/stage -o .lake/build/lib/lean/<module>.olean .lake/stage/<module>.lean
# Records exit, wall, peak RSS, swaps, source sha256 and olean sha256.
# Usage: ./nvr_compile.sh path/to/A.lean [...]   (dependency order)
# NVR_OUT=/some/dir overrides the olean directory (used for the rev1-source negative control).
set -u
out_dir="${NVR_OUT:-.lake/build/lib/lean}"
mkdir -p "$out_dir" .lake/build/lib/lean .lake/stage
for f in "$@"; do
  m=$(basename "$f" .lean)
  src=$(shasum -a 256 "$f" | cut -d' ' -f1)
  cp "$f" ".lake/stage/$m.lean"
  [ "$(shasum -a 256 ".lake/stage/$m.lean" | cut -d' ' -f1)" = "$src" ] || { echo "stage copy mismatch $f"; exit 3; }
  out=$( { /usr/bin/time -l lake env lean --root=.lake/stage -o "$out_dir/$m.olean" ".lake/stage/$m.lean" ; } 2>&1 )
  rc=$?
  wall=$(printf '%s\n' "$out" | awk '/ real /{print $1}')
  rss=$(printf '%s\n' "$out" | awk '/maximum resident set size/{print $1}')
  swaps=$(printf '%s\n' "$out" | awk '/ swaps$/{print $1}')
  ol=-; [ $rc -eq 0 ] && ol=$(shasum -a 256 "$out_dir/$m.olean" | cut -d' ' -f1)
  printf '%s\texit=%s\twall_s=%s\tpeak_rss_bytes=%s\tswaps=%s\tsrc_sha256=%s\tolean_sha256=%s\n' \
    "$f" "$rc" "$wall" "$rss" "$swaps" "$src" "$ol" | tee -a "${NVR_LOG:-NVR_COMPILE.tsv}"
  printf '%s\n' "$out" | grep -v '^ *[0-9]\+  [a-z]' | grep -v ' real ' | head -80
  [ $rc -ne 0 ] && [ -z "${NVR_KEEP_GOING:-}" ] && exit $rc
done
exit 0
