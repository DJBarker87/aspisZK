#!/usr/bin/env bash
# Future-version one-transaction verifier: deploy and finalize (PIN2-DEPLOY-TPU.sh adapted).
# usage: FV_deploy.sh <rpc-url> <solana-cli> <payer-key> <program-keypair> <buffer-keypair> <elf>
# The buffer keypair is retained, so an interrupted deploy resumes from the same buffer and an
# abandoned one can be closed (solana program close <buffer>) to return its rent to the payer.
# --final revokes the upgrade authority: the ProgramData rent is locked from that point.
set -uo pipefail
URL=$1; SOLANA=$2; P=$3; K=$4; B=$5; ELF=$6
echo "payer balance: $($SOLANA balance -k $P --url $URL)"
echo "elf: $(shasum -a 256 $ELF 2>/dev/null || sha256sum $ELF)"
ok=0
for i in 1 2 3 4 5 6; do
  echo "== verifier deploy attempt $i $(date -u +%H:%M:%S)"
  $SOLANA program deploy --url $URL -k $P --program-id $K --buffer $B --final --max-sign-attempts 300 --with-compute-unit-price 10000 $ELF && { echo VERIFIER_DEPLOYED; ok=1; break; }
  sleep 30
done
$SOLANA program show --url $URL $($SOLANA-keygen pubkey $K) || true
echo "payer balance after: $($SOLANA balance -k $P --url $URL)"
[ $ok = 1 ] && echo DEPLOY_END_OK || { echo DEPLOY_END_FAILED; exit 1; }
