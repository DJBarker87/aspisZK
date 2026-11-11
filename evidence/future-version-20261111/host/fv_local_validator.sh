#!/bin/bash
# Runs INSIDE a scope. Local validator for the one-transaction rehearsal: devnet's feature set and
# the deployed registry, Pool and upload programs cloned (read-only RPC to devnet); the verifier is
# NOT preloaded, it is deployed and finalized by the same script the devnet run uses.
# Usage: fv_local_validator.sh <name>
set -euo pipefail
W=/home/dombarker/project-offloads/future-version-20261111
L=$W/$1; CLI=/home/dombarker/project-offloads/codex-cx-devnet-rehearse-20261029/NDZ_runtime/extracted/solana-release/bin
cd $L
export NO_DNA=1
exec taskset -c 4-7 "$CLI/solana-test-validator" \
  --ledger $L/ledger --limit-ledger-size 1000000 --bind-address 127.0.0.1 --rpc-port 18957 --faucet-port 19957 \
  --url https://api.devnet.solana.com --clone-feature-set \
  --clone-upgradeable-program 9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q \
  --clone-upgradeable-program 37hdATMkskKX1hiCWhz4nnzkD7GauYwX8EQwcpUDb3Zt \
  --clone-upgradeable-program 9DYn3ykkW6JEgYVKst7y7Jd9SqxSjoSNUVTgnGCHWqx5 \
  --account "$($CLI/solana-keygen pubkey keys/payer.json)" payer-genesis.json --quiet
