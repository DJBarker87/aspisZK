#!/bin/bash
# Runs INSIDE a scope. Aspis freeze rehearsal: local validator with devnet's feature set, the deployed
# registry and upload programs cloned (read-only RPC to devnet), and the NEW Pool ELF placed at the
# address the frozen verifier embeds (upgradeable, authority = the rehearsal payer). The verifier is
# not preloaded: the run deploys and finalizes it with the script the devnet run uses.
# fv_local_validator.sh with the Pool as a parameter (that script cloned the deployed Pool).
# Usage: fv_frz_local_validator.sh <name> <pool-program-id> <pool-elf>
set -euo pipefail
W=/home/dombarker/project-offloads/future-version-20261111
L=$W/$1; POOL=$2; POOL_ELF=$3
CLI=/home/dombarker/project-offloads/codex-cx-devnet-rehearse-20261029/NDZ_runtime/extracted/solana-release/bin
cd $L
export NO_DNA=1
exec taskset --cpu-list 0-3 "$CLI/solana-test-validator" \
  --ledger $L/ledger --limit-ledger-size 1000000 --bind-address 127.0.0.1 --rpc-port 18957 --faucet-port 19957 \
  --url https://api.devnet.solana.com --clone-feature-set \
  --clone-upgradeable-program 9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q \
  --clone-upgradeable-program 9DYn3ykkW6JEgYVKst7y7Jd9SqxSjoSNUVTgnGCHWqx5 \
  --upgradeable-program $POOL $POOL_ELF "$($CLI/solana-keygen pubkey keys/payer.json)" \
  --account "$($CLI/solana-keygen pubkey keys/payer.json)" payer-genesis.json --quiet
