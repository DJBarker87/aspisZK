#!/bin/bash
# Round 4: the kept set (W20 = W13 + G2 + G6) and W21 = W20 + H1 as plain builds on six fixtures, and the
# one-transaction adapter build with H1 replayed on the two recorded devnet settlements.
W=/home/dombarker/project-offloads/future-version-20261111
cd $W
K=private-leaf-salts,future-fast-kmul,future-fast-prepared,future-fast-square,future-validated-decode,future-merkle-single-pass,future-tight-base,future-tight-weights,future-lazy-boundary,future-d-inactive-tensor,future-d-pair-expansion,future-merkle-in-place,future-lazy-horner,future-fold-shared
run() { # <attempt> <features>
  bash fv_scope.sh $1 1800 bash $W/fv_build.sh $1 $2 || { echo "BUILD_FAILED $1" > $W/ALL14_DONE; exit 1; }
  for f in transfer-13 transfer-255 transfer-1023 withdrawal-13 withdrawal-255 withdrawal-1023; do bash fv_scope.sh M14-$1-$f 300 bash $W/fv_run.sh $1 $f; done
}
run W20-kept $K
run W21-h1 $K,future-lean-dot
bash fv_scope.sh A2-onetx-h1 1800 bash $W/fv_build_adapter.sh A2-onetx-h1 pool-adapter,future-one-tx,$K,future-lean-dot || { echo ADAPTER_BUILD_FAILED > $W/ALL14_DONE; exit 1; }
bash fv_scope.sh R2-A2-onetx-h1-transfer 600 bash $W/fv_replay.sh A2-onetx-h1 transfer
bash fv_scope.sh R2-A2-onetx-h1-withdrawal 600 bash $W/fv_replay.sh A2-onetx-h1 withdrawal
echo done > $W/ALL14_DONE
