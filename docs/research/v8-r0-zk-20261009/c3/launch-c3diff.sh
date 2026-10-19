#!/bin/bash
# c3/launch-c3diff.sh <tag> : Z9d differential run (D49.4 C3) on the build host, in a capped scope
# (MemoryHigh 6G / MemoryMax 8G / MemorySwapMax 0).  Gate: no other cargo/rustc/lean/aeneas/charon job.
set -u
S=/home/dombarker/project-offloads/aspis-r0-checker-extract-20261019; TAG=$1
cd $S/repo
echo "GATE_CHECK $(date -Is)"
if ps -eo cmd | grep -E 'cargo|rustc|lean |aeneas|charon|target/release/' | grep -v grep | grep -v launch-c3diff; then echo GATE_FAIL; exit 3; fi
echo GATE_OK; free -g | head -2
/usr/bin/time -v -o $S/c3diff-$TAG-time.txt systemd-run --user --scope --unit=aspis-c3diff-$TAG \
  -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 \
  python3 docs/research/v8-r0-zk-20261009/z4/run-c3diff.py --out $S/c3diff-$TAG --revision $TAG
echo "EXIT $? $(date -Is)"
