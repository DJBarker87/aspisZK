#!/usr/bin/env bash
# Aspis freeze: deploy the Pool program, UPGRADEABLE, upgrade authority = the payer. Nothing is
# finalized, so the ProgramData rent stays recoverable (solana program close) while the payer key
# is kept. The buffer keypair is retained: an interrupted deploy resumes from the same buffer and
# an abandoned one can be closed to return its rent.
# usage: ASPIS_deploy_pool.sh <rpc-url> <solana-cli> <payer-key> <program-keypair> <buffer-keypair> <elf>
set -uo pipefail
URL=$1; SOLANA=$2; P=$3; K=$4; B=$5; ELF=$6
echo "payer balance: $($SOLANA balance -k $P --url $URL)"
echo "elf: $(shasum -a 256 $ELF 2>/dev/null || sha256sum $ELF)"
ok=0
for i in 1 2 3 4 5 6; do
  echo "== pool deploy attempt $i $(date -u +%H:%M:%S)"
  $SOLANA program deploy --url $URL -k $P --program-id $K --buffer $B --upgrade-authority $P --max-sign-attempts 300 --with-compute-unit-price 10000 $ELF && { echo POOL_DEPLOYED; ok=1; break; }
  sleep 30
done
$SOLANA program show --url $URL $($SOLANA-keygen pubkey $K) || true
echo "payer balance after: $($SOLANA balance -k $P --url $URL)"
[ $ok = 1 ] && echo DEPLOY_END_OK || { echo DEPLOY_END_FAILED; exit 1; }
