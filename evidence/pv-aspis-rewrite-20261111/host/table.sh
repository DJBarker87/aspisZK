#!/bin/bash
# Runs INSIDE one capped scope. Usage: table.sh <tag> <run> <mode table|retry|fail> <first-seed> <count>
# Gate B: mode table = fixture proofs for both operations; retry = the same plus the retry loop on a
# fresh ledger root; fail = the forced failing paths on a fresh ledger root. Not pinned to CPUs 0-3
# (the SBF builds of every stream are pinned there).
set -u
W=/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111
TAG=$1; RUN=$2; OUT=$W/out/$TAG
test ! -e $OUT/table-$RUN.txt || { echo "exists"; exit 2; }
case $3 in
  table) $OUT/pv_bytes_gate table $4 $5 > $OUT/table-$RUN.txt || exit 1;;
  retry) $OUT/pv_bytes_gate table $4 $5 $W/ledgers/$TAG-$RUN > $OUT/table-$RUN.txt || exit 1;;
  fail)  $OUT/pv_bytes_gate fail $4 $5 $W/ledgers/$TAG-$RUN > $OUT/table-$RUN.txt || exit 1;;
esac
sha256sum $OUT/table-$RUN.txt
wc -l $OUT/table-$RUN.txt
