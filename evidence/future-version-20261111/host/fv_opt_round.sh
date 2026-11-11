#!/bin/bash
# Optimisation rounds: build each candidate tree, replay the two recorded settlements and the redirect
# attempts against it (fv_round7.sh pattern), then one worst-case run with X1 and every candidate ELF.
# Usage: fv_opt_round.sh <round-tag> <name>...
#   each <name> has its changed files staged under opt/stage/<name>/ (crates/..., programs/...); the
#   tree src-opt-<name> is a copy of src-xp1 with those files over it; its patch is written to
#   opt/patches/<name>.patch (diff -ruN against src-xp1, crates and programs only).
# Time is expected in compilation (one SBF build of about a minute per candidate); each replay is
# seconds; the worst-case run proves one fixture payment (tens of seconds) and runs each ELF four times.
W=/home/dombarker/project-offloads/future-version-20261111
cd $W
TAG=$1; shift
K=pool-adapter,future-one-tx-lean,private-leaf-salts,future-fast-kmul,future-fast-prepared,future-fast-square,future-validated-decode,future-merkle-single-pass,future-tight-base,future-tight-weights,future-lazy-boundary,future-d-inactive-tensor,future-d-pair-expansion,future-merkle-in-place,future-lazy-horner,future-fold-shared
D=$W/OPT_ROUND_$TAG.done; rm -f $D
mkdir -p opt/replays opt/redirect opt/patches
ELFS="X1=$W/out/X1-rewrites/artifacts/aspis_r1_cost_probe_program.so"
for N in "$@"; do
  T=src-opt-$N
  if [ ! -d $T ]; then cp -a src-xp1 $T && cp -a opt/stage/$N/. $T/; fi
  { diff -ruN src-xp1/crates $T/crates; diff -ruN src-xp1/programs $T/programs; } > opt/patches/$N.patch
  bash fv_slot.sh OPT-B-$N 3000 bash $W/fv_build_adapter_src.sh OPT-$N $K $T || { echo "BUILD_FAILED $N" >> $D; continue; }
  E=$W/out/OPT-$N/artifacts/aspis_r1_cost_probe_program.so
  echo "elf $N $(cut -d' ' -f1 out/OPT-$N/so.sha256) $(awk '{print $5}' out/OPT-$N/so.size)" >> $D
  for op in transfer withdrawal; do
    bash fv_slot.sh OPT-R-$N-$op 600 bash -c "ASPIS_SOURCE_REVISION=\$(cat $W/SOURCE_REVISION)+$T $W/target/native/release/one_tx_replay $W/devnet/PIN2_TRANSACTIONS.json $W/devnet/pool.so $W/devnet/verifier-pin2.so $E $op $W/opt/replays/$N-$op.json"
    echo "replay $N $op exit $?" >> $D
  done
  bash fv_slot.sh OPT-RD-$N 600 bash -c "ASPIS_SOURCE_REVISION=\$(cat $W/SOURCE_REVISION)+$T $W/target/native/release/one_tx_redirect $W/devnet/PIN2_TRANSACTIONS.json $W/devnet/pool.so $E $W/opt/redirect/$N-withdrawal.json"
  echo "redirect $N exit $?" >> $D
  ELFS="$ELFS $N=$E"
done
bash fv_slot.sh OPT-W-$TAG 5400 bash -c "ASPIS_SOURCE_REVISION=\$(cat $W/SOURCE_REVISION) taskset --cpu-list 0-3 $W/worst/one_tx_worst-src $W/devnet/PIN2_TRANSACTIONS.json $W/devnet/pool.so $W/opt/worst-$TAG.json withdrawal:255:60:full $ELFS"
echo "worst exit $?" >> $D
sha256sum $W/worst/one_tx_worst-src opt/worst-$TAG.json opt/patches/*.patch >> $D 2>&1
echo DONE >> $D
