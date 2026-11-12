#!/bin/bash
# X7 driver: the scripted clean-emission check of one source tree, both on-chain programs, rerunnable unchanged on
# later commits. Runs on the build host (not itself in a scope); every heavy command runs in ONE fv_slot.sh scope at a
# time (MemoryHigh 6G, MemoryMax 8G, no swap), attempt names X7-<label>-emit and X7-<label>-sbf (single use).
#
# Usage (from anywhere on the host):
#   bash W/x7/bin/fv_emit_candidate.sh <tree name under W> <label> [--ref <label of a reference SBF run>] [--sbf-only] [--no-sbf]
#        [--post <n>]   (gates, tables and manifest again on an existing run, in scope X7-<label>-post<n>; no emission)
#   KEEP_TARGET=1 in the environment keeps the Charon cargo target directory W/x7/target/<label> (default: deleted);
#   SKIP_CONSTEVAL=1 skips the constants step in a --post run (it needs that directory).
# The tree is made first from a commit with fv_frz_tree.sh:
#   git archive <commit> crates programs tools Cargo.toml Cargo.lock | ssh host 'bash W/fv_frz_tree.sh <tree> <commit>'
# Output: W/x7/runs/<label>/ (steps.tsv, tools.tsv, tree/, verifier/, pool/, gates/, gates.txt, rows and externals
# tables per program, shared.tsv, constants.json, MANIFEST.json, sbf/, stack-compare.tsv), receipts copied to
# W/x7/runs/<label>/receipt-*, exit code in W/x7/runs/<label>.status (written last).
# Stops before a scope when the workspace disk has less than 35 GiB free.
set -u
W=/home/dombarker/project-offloads/future-version-20261111
B=$(cd $(dirname $0) && pwd)
T=$1; L=$2; shift 2
REF=""; SBF=1; EMIT=1; POST=""
while [ $# -gt 0 ]; do
  case $1 in --ref) REF=$2; shift 2;; --sbf-only) EMIT=0; shift;; --no-sbf) SBF=0; shift;; --post) POST=$2; EMIT=0; SBF=0; shift 2;; *) echo "unknown $1"; exit 2;; esac
done
O=$W/x7/runs/$L; mkdir -p $O
disk() { local f=$(df -BG --output=avail $W | tail -1 | tr -dc 0-9); echo "$(date -u +%FT%TZ) free ${f}G" >> $O/disk.log; [ $f -ge 35 ]; }
rc=0
if [ $EMIT = 1 ]; then
  disk || { echo 4 > $O.status; echo "disk below 35 GiB"; exit 4; }
  bash $W/fv_slot.sh X7-$L-emit 10800 env KEEP_TARGET=${KEEP_TARGET:-0} PHASE=all bash $B/fv_emit_job.sh $T $L > $O/launch-emit.log 2>&1; rc=$?
  cp -r $W/receipts/X7-$L-emit $O/receipt-emit 2>/dev/null
fi
if [ -n "$POST" ]; then
  bash $W/fv_slot.sh X7-$L-post$POST 3600 env KEEP_TARGET=${KEEP_TARGET:-0} SKIP_CONSTEVAL=${SKIP_CONSTEVAL:-0} PHASE=post bash $B/fv_emit_job.sh $T $L > $O/launch-post$POST.log 2>&1; rc=$?
  cp -r $W/receipts/X7-$L-post$POST $O/receipt-post$POST 2>/dev/null
fi
if [ $SBF = 1 ]; then
  disk || { echo 4 > $O.status; echo "disk below 35 GiB"; exit 4; }
  bash $W/fv_slot.sh X7-$L-sbf 5400 bash $B/fv_emit_sbf.sh $T $L > $O/launch-sbf.log 2>&1; r2=$?
  cp -r $W/receipts/X7-$L-sbf $O/receipt-sbf 2>/dev/null
  [ $rc -ne 0 ] || rc=$r2
fi
if [ -n "$REF" ]; then
  python3 -I $B/fv_emit_stack.py $W/x7/runs/$REF/sbf $O/sbf $O > $O/stack-compare.tsv 2> $O/stack-compare.err
fi
disk
echo $rc > $O.status
exit $rc
