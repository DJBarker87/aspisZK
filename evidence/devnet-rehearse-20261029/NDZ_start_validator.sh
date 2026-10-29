#!/usr/bin/env bash
set -euo pipefail
cd /home/dombarker/project-offloads/codex-cx-devnet-rehearse-20261029/evidence/devnet-rehearse-20261029
export NO_DNA=1
cli=../../NDZ_runtime/extracted/solana-release/bin
payer=$($cli/solana-keygen pubkey keys/payer.json)
python3 - "$payer" <<'PY'
import json,sys
json.dump({'pubkey':sys.argv[1],'account':{'lamports':18353204080,'data':['','base64'],'owner':'11111111111111111111111111111111','executable':False,'rentEpoch':0,'space':0}},open('NDZ_payer-genesis.json','w'))
PY
cat /proc/self/cgroup > NDZ_final-validator-cgroup.txt
cg=$(awk -F: '$1=="0" {print $3}' /proc/self/cgroup)
for p in memory.high memory.max memory.swap.max; do cat "/sys/fs/cgroup$cg/$p" > "NDZ_final-validator-$p"; done
# Cloning sends only read-only RPC queries to devnet. Every later signer uses loopback.
exec taskset -c 0-3 /usr/bin/time -v -o NDZ_final-validator.time "$cli/solana-test-validator" \
  --ledger keys/NDZ_final_ledger --limit-ledger-size 1000000 --bind-address 127.0.0.1 --rpc-port 18995 --faucet-port 19995 \
  --url https://api.devnet.solana.com --clone-feature-set \
  --clone-upgradeable-program BmsNikL97uF7bb1hMnJxsas7a9LjjK8vvT5Q1b7W34Qs \
  --clone-upgradeable-program 9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q \
  --clone-upgradeable-program 3jEFrv5Npn3RmFMW1Cbzq5yEiLdeFB5vbBGmnfoqK9vN \
  --account "$payer" NDZ_payer-genesis.json --quiet
