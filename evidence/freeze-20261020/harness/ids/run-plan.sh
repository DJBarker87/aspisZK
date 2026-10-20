#!/bin/sh
set -eu
# usage: run-plan.sh <phase> <driver> <verifier.so>
# Pool B1-style scenario runs on the regenerated (adopted-format) fixtures,
# each with --reuse of the saved proof/statement, split 10, TxV1, one capped
# scope and receipt per run: replays of the six fixtures, double spend
# (replay, with and without a prefunded marker), rent-prefunded marker,
# wrong release, stale lane, proof rejection, withdrawal CPI failure.
H=/home/dombarker/project-offloads/codex-cx-pin-20261020
X=$H/runs/adopt
P=$1; D=$2; V=$3
POOL=${POOL:-/home/dombarker/project-offloads/codex-r1-cu-bound2-20261019/artifacts/pool/aspis_pool.so}
REG=/home/dombarker/project-offloads/active-mask-basis-sbf-20261017/artifacts/aux-current/registry/aspis_registry.so
mkdir -p $H/runs/$P
run() { # label kind fixture scenario [extra...]
  L=$1; K=$2; FX=$3; S=$4; shift 4; T=$H/runs/$P/$L; mkdir -p $T
  $H/harness/capped-run.sh $P-$L "one scenario replay: seconds" $H -- \
    $D $POOL $V $REG $T/evidence.json $T/task $K $S --pairs ${FX##*-} --reuse $X/$FX/task/r1-s2-proof.bin $X/$FX/task/r1-s2-public-asf8.bin --split 10 --tx-version v1 "$@"
}
# Six success fixtures were already measured by continue.py; do not repeat.
for k in transfer withdrawal; do
  run replay-$k-13 $k $k-13 replay
  run replay-prefund1-$k-13 $k $k-13 replay --prefund-marker 1
  run prefund-rent-$k-13 $k $k-13 success --prefund-marker 2338560
  run wrong-release-$k-13 $k $k-13 wrong-release
  run stale-lane-$k-13 $k $k-13 stale-lane
  run proof-rejection-$k-13 $k $k-13 proof-rejection
done
run withdrawal-cpi-failure-13 withdrawal withdrawal-13 withdrawal-cpi-failure
