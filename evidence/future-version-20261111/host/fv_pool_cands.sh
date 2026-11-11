#!/bin/bash
# Pool page zero check: build candidate Pool trees with the deployed recipe (fv_pool_build.sh).
# Usage: fv_pool_cands.sh <name>...
#   each <name> has its changed files staged under pool-stage/<name>/ (programs/aspis-pool/...); the
#   tree src-pool-<name> is a copy of src-xp1 with those files over it; its patch is written to
#   pool-patches/<name>.patch (diff -ruN against src-xp1, programs/aspis-pool only).
# Time is expected in compilation: one cold SBF build of the Pool per candidate (about four minutes,
# own target directory per tree).
W=/home/dombarker/project-offloads/future-version-20261111
cd $W
mkdir -p pool-patches
for N in "$@"; do
  T=src-pool-$N
  if [ ! -d $T ]; then cp -a src-xp1 $T && cp -a pool-stage/$N/. $T/; fi
  diff -ruN src-xp1/programs/aspis-pool $T/programs/aspis-pool > pool-patches/$N.patch
  bash fv_slot.sh PL-build-$N 3000 bash $W/fv_pool_build.sh PL-$N $T
  echo "build $N exit $? $(cat out/PL-$N/so.sha256 2>/dev/null) $(awk '{print $5}' out/PL-$N/so.size 2>/dev/null)"
done
