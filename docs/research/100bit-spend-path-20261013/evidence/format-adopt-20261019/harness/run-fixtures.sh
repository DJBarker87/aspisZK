#!/bin/sh
# usage: run-fixtures.sh <phase> <driver> <verifier.so> [env assignments...]
# Re-proves the six saved fixtures' witnesses (same --pairs/kind as the Pool B1
# replay; the generated ASF8 must equal the saved fixture's public file) with
# fresh OS entropy, each run in its own capped scope with a receipt. The
# driver saves the new proof and statement in the task dir.
set -e
H=/home/dombarker/project-offloads/codex-r1-format-adopt-20261019
F=/home/dombarker/project-offloads/aspis-r1-rollover-measurement-20261019/fixtures
P=$1; D=$2; V=$3; shift 3
POOL=${POOL:-/home/dombarker/project-offloads/codex-r1-cu-bound2-20261019/artifacts/pool/aspis_pool.so}
REG=/home/dombarker/project-offloads/active-mask-basis-sbf-20261017/artifacts/aux-current/registry/aspis_registry.so
mkdir -p $H/runs/$P
for kind in transfer withdrawal; do for n in 13 255 1023; do
  L=$kind-$n; T=$H/runs/$P/$L; mkdir -p $T
  env "$@" R1_PROOF_SIZE_EXPECT_PUBLIC=$F/$L/r1-s2-public-asf8.bin $H/harness/capped-run.sh $P-$L "one fixture: prove ~10 s + replay" $H -- \
    $D $POOL $V $REG $T/evidence.json $T/task $kind success --pairs $n --mask-entropy os --split 10 --tx-version v1 || echo "RUN-FAILED $L"
done; done
