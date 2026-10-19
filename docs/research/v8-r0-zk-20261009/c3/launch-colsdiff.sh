#!/bin/bash
# c3/launch-colsdiff.sh <tag> : D72.2 column-writer differential (z9d builder_diff, builders 5/6 added)
# in the branch workspace codex-r1p-column-writers-20261019, in a capped scope (MemoryHigh 6G /
# MemoryMax 8G / MemorySwapMax 0 / TasksMax 64), optimized (release, overflow checks on).
# Expected time: compilation of the z4 probe (cold target), then per configuration emit +
# z9c check + builders + C3 check (D66: 23-210 s each).
set -u
S=/home/dombarker/project-offloads/codex-r1p-column-writers-20261019; TAG=$1
cd $S/repo
echo "START $TAG $(date -Is) rev=$(cat REVISION)"
/usr/bin/time -v -o $S/colsdiff-$TAG-time.txt systemd-run --user --scope --unit=aspis-colsdiff-$TAG-$$ \
  -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 \
  python3 docs/research/v8-r0-zk-20261009/z4/run-c3diff.py --out $S/colsdiff-$TAG --revision "$(cat REVISION)"
echo "EXIT $? $(date -Is)"
