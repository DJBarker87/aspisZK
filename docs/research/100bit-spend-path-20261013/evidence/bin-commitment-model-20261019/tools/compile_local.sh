#!/bin/bash
# Focused local compile of one Bin* module (local-lean rules: flock, -j1 -M4400,
# memory precheck, /usr/bin/time -l receipts). Usage: compile_local.sh Module
set -u
M="$1"
WT=/Users/dominic/ZK/.worktrees/r1-commit-model
SRCDIR=$WT/docs/research/100bit-spend-path-20261013/lean
EV=$WT/docs/research/100bit-spend-path-20261013/evidence/bin-commitment-model-20261019
OBJ=/tmp/r1-commit-model-20261019-objects
STAGE=/tmp/r1-commit-model-20261019-src
LEAN=/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean
BASE_LP=$(cat "$EV/tools/base-lean-path.txt")
mkdir -p "$OBJ" "$STAGE" "$EV/$M"
cp "$SRCDIR/$M.lean" "$STAGE/$M.lean"
SHA=$(shasum -a 256 "$STAGE/$M.lean" | cut -d' ' -f1)
while true; do
  FREE=$(vm_stat | awk '/Pages free/ {gsub("\\.","",$3); f=$3} /Pages inactive/ {gsub("\\.","",$3); i=$3} END {print (f+i)*16384}')
  if [ "$FREE" -ge 10737418240 ]; then break; fi
  echo "waiting for memory: $FREE" >&2; sleep 60
done
SWAP=$(sysctl vm.swapusage)
START=$(date -u +%Y-%m-%dT%H:%M:%SZ)
cd "$STAGE"
LEAN_PATH="$OBJ:$BASE_LP" python3 -I "$EV/tools/flock.py" /tmp/aspis-local-lean.lock /usr/bin/time -l "$LEAN" -j1 -M4400 -DElab.async=false -o "$OBJ/$M.olean" "$STAGE/$M.lean" > "$EV/$M/lean.log" 2> "$EV/$M/time.log"
EXIT=$?
python3 -I "$EV/tools/receipt.py" "$M" "$SHA" "$EXIT" "$START" "$SWAP" "$OBJ" "$EV/$M" "$OBJ:$BASE_LP"
exit $EXIT
