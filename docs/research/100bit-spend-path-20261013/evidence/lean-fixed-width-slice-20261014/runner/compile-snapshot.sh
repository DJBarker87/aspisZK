#!/usr/bin/env bash
# Preserve the exact source before invoking the unchanged capped NUC runner.
# Usage: compile-snapshot.sh MODULE UNIQUE_ATTEMPT
set -euo pipefail
base=/home/dombarker/project-offloads/aspis-r1-concrete-decoder-20261013
target=${1:?module required}
attempt=${2:?unique attempt required}
[[ "$target" =~ ^[A-Za-z0-9_]+$ && "$attempt" =~ ^[A-Za-z0-9_-]+$ ]] || exit 64
source_file="$base/sources/$target.lean"
snapshot="$base/evidence/$target-$attempt.source.lean"
# Refuse to overwrite historical evidence, including failed attempts.
(set -C; cat "$source_file" > "$snapshot")
sha256sum "$snapshot" > "$base/evidence/$target-$attempt.source.sha256"
if bash "$base/compile-one.sh" "$target" "$attempt"; then
  result=0
else
  result=$?
fi
# A source mutation during compilation invalidates this attempt.
cmp -- "$source_file" "$snapshot"
exit "$result"
