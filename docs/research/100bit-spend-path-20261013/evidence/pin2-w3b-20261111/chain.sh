#!/bin/zsh
# build the listed modules in order; skip any whose overlay object already exists (another worker built it)
W=/Users/dominic/ZK/.worktrees/pin2-lean/docs/research/100bit-spend-path-20261013/evidence/pin2-w3b-20261111
OV=$HOME/aspis-lead-infra/l187-closure/overlay-PIN2
for m in $(cat $1); do p=${m//.//}
  if [ -L $OV/$p.olean ]; then echo "STOP $m: overlay object is a symlink to the stale closure object"; exit 2; fi
  if [ -e $OV/$p.olean ]; then echo "SKIP $m (present in overlay)"; continue; fi
  out=$($W/run.sh $p "unchanged source, rebuild in import order (W3b item 4)" 8); echo "$out" | head -1
  echo "$out" | head -1 | grep -q 'exit=0' || { echo "$out"; echo STOP; exit 1; }
done
