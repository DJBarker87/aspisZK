#!/bin/bash
# Runs INSIDE a scope. Aspis freeze rehearsal: the devnet sequence against the local validator started by
# fv_frz_local_validator.sh: deploy and finalize the verifier, preflight, the one-transaction spend run
# (two payments with the negative tests), rent cleanup. fv_local_run.sh with the source tree (run scripts
# are read from it), the verifier ELF, the Pool and the client binary as parameters.
# Second form: the spend script is a parameter (the freeze run script with the redirect attempts).
# Usage: fv_frz_local_run2.sh <name> <verifier-elf> <pool-program-id> <pool-elf> <client-binary> <source-dir-name> <spend-script>
set -uo pipefail
W=/home/dombarker/project-offloads/future-version-20261111
L=$W/$1; VERIFIER=$2; POOL=$3; POOL_ELF=$4; CLIENT=$5; S=$6; SPEND=$7
CLI=/home/dombarker/project-offloads/codex-cx-devnet-rehearse-20261029/NDZ_runtime/extracted/solana-release/bin
URL=http://127.0.0.1:18957; D=$W/$S/evidence/future-version-20261111/devnet
export NO_DNA=1 PYTHONDONTWRITEBYTECODE=1 PYTHONPATH=$W/$S/scripts:$W/$S/evidence/pin2-upload-20261110/devnet:$D
step() { echo "== $1 $(date -u +%H:%M:%S)"; }
step wait-validator
for i in $(seq 1 90); do curl -s $URL -X POST -H 'Content-Type: application/json' -d '{"jsonrpc":"2.0","id":1,"method":"getHealth"}' | grep -q '"ok"' && break; sleep 2; done
step rent; curl -s $URL -X POST -H 'Content-Type: application/json' -d '{"jsonrpc":"2.0","id":1,"method":"getMinimumBalanceForRentExemption","params":[1768]}'; echo
step pool; $CLI/solana program show --url $URL $POOL || exit 10
step deploy; bash $D/FV_deploy.sh $URL $CLI/solana $L/keys/payer.json $L/keys/verifier.json $L/keys/buffer.json $VERIFIER > $L/out/deploy.log 2>&1 || { tail -30 $L/out/deploy.log; exit 11; }
tail -12 $L/out/deploy.log
step config; python3 $W/fv_frz_local_config.py $1 $VERIFIER $POOL $POOL_ELF $CLIENT $S || exit 12
V=$($CLI/solana-keygen pubkey $L/keys/verifier.json)
for i in $(seq 1 60); do
  curl -s $URL -X POST -H 'Content-Type: application/json' -d '{"jsonrpc":"2.0","id":1,"method":"getAccountInfo","params":["'$V'",{"encoding":"base64","commitment":"finalized","dataSlice":{"offset":0,"length":0}}]}' | grep -q '"executable":true' && break
  sleep 2
done
step preflight; python3 $D/FV_preflight.py $L/out/FV_local.json $L/out/FV_PREFLIGHT.json || exit 13
step spend; python3 $SPEND $L/out/FV_local.json $L/out/FV_spend || exit 14
step cleanup; python3 $D/FV_cleanup.py $L/out/FV_local.json $L/out/FV_spend || exit 15
step balance; $CLI/solana balance -k $L/keys/payer.json --url $URL --lamports
echo LOCAL_RUN_OK
