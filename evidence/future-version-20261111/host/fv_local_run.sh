#!/bin/bash
# Runs INSIDE a scope. The devnet sequence against the local validator: deploy and finalize the
# verifier, preflight, the one-transaction spend run (two payments with negatives), rent cleanup.
# Usage: fv_local_run.sh <name> <adapter-attempt>
set -uo pipefail
W=/home/dombarker/project-offloads/future-version-20261111
L=$W/$1; CLI=/home/dombarker/project-offloads/codex-cx-devnet-rehearse-20261029/NDZ_runtime/extracted/solana-release/bin
URL=http://127.0.0.1:18957; D=$W/src/evidence/future-version-20261111/devnet
export NO_DNA=1 PYTHONDONTWRITEBYTECODE=1 PYTHONPATH=$W/src/scripts:$W/src/evidence/pin2-upload-20261110/devnet:$D
step() { echo "== $1 $(date -u +%H:%M:%S)"; }
step rent; curl -s $URL -X POST -H 'Content-Type: application/json' -d '{"jsonrpc":"2.0","id":1,"method":"getMinimumBalanceForRentExemption","params":[1768]}'; echo
step deploy; bash $D/FV_deploy.sh $URL $CLI/solana $L/keys/payer.json $L/keys/verifier.json $L/keys/buffer.json $W/out/$2/artifacts/aspis_r1_cost_probe_program.so > $L/out/deploy.log 2>&1 || { tail -30 $L/out/deploy.log; exit 11; }
tail -12 $L/out/deploy.log
step config; python3 $W/fv_local_config.py $1 $2 || exit 12
step preflight; python3 $D/FV_preflight.py $L/out/FV_local.json $L/out/FV_PREFLIGHT.json || exit 13
step spend; python3 $D/FV_spend.py $L/out/FV_local.json $L/out/FV_spend || exit 14
step cleanup; python3 $D/FV_cleanup.py $L/out/FV_local.json $L/out/FV_spend || exit 15
step balance; $CLI/solana balance -k $L/keys/payer.json --url $URL --lamports
echo LOCAL_RUN_OK
