#!/bin/bash
# Aspis freeze rehearsal driver (fv_all20.sh adapted; both scopes through fv_slot.sh): prepare throwaway
# keys, start the local validator with the new Pool ELF at the address the verifier embeds, run the devnet
# sequence against it, stop the validator.
# Usage: fv_frz_local.sh <name> <verifier-elf> <pool-program-id> <pool-elf> <client-binary> <source-dir-name>
W=/home/dombarker/project-offloads/future-version-20261111
cd $W
N=$1
bash fv_local_prepare.sh $N || { echo PREPARE_FAILED > $W/DONE_$N; exit 1; }
(bash fv_slot.sh V-$N 6000 bash $W/fv_frz_local_validator.sh $N $3 $4 > $W/validator-$N.log 2>&1 &)
ok=0
for i in $(seq 1 120); do
  sleep 5
  curl -s -m 3 http://127.0.0.1:18957 -X POST -H 'Content-Type: application/json' -d '{"jsonrpc":"2.0","id":1,"method":"getHealth"}' | grep -q '"ok"' && { ok=1; break; }
done
[ $ok = 1 ] || { echo VALIDATOR_NOT_HEALTHY > $W/DONE_$N; pkill -f "solana-test-validator --ledger $W/$N/ledger"; exit 1; }
bash fv_slot.sh L-$N 5400 bash $W/fv_frz_local_run.sh $N $2 $3 $4 $5 $6; rc=$?
pkill -f "solana-test-validator --ledger $W/$N/ledger"
echo "local run exit $rc" > $W/DONE_$N
