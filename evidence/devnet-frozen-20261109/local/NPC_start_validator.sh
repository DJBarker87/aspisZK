#!/usr/bin/env bash
# NPC_ B2: NDZ_start_validator.sh adapted. Differences: own root/ledger/port; the verifier
# CSnhzGdH (immutable on devnet, ELF 63ad3e9c) is cloned instead of deployed; the Pool program
# BmsNik is loaded from the frozen ELF e0e49c34 with its devnet upgrade authority Xjb7 (public key
# only) instead of cloning the pre-removal 121f3e29. Cloning sends only read-only RPC to devnet.
set -euo pipefail
L=/home/dombarker/project-offloads/codex-cx-devnet2-20261109/local
cd "$L"
export NO_DNA=1
cli=/home/dombarker/project-offloads/codex-cx-devnet-rehearse-20261029/NDZ_runtime/extracted/solana-release/bin
payer=$($cli/solana-keygen pubkey keys/payer.json)
python3 - "$payer" <<'PY'
import json,sys
json.dump({'pubkey':sys.argv[1],'account':{'lamports':18353204080,'data':['','base64'],'owner':'11111111111111111111111111111111','executable':False,'rentEpoch':0,'space':0}},open('NPC_payer-genesis.json','w'))
PY
cat /proc/self/cgroup > out/NPC_validator-cgroup.txt
cg=$(awk -F: '$1=="0" {print $3}' /proc/self/cgroup)
for p in memory.high memory.max memory.swap.max pids.max; do cat "/sys/fs/cgroup$cg/$p" > "out/NPC_validator-$p"; done
exec taskset -c 0-3 /usr/bin/time -v -o out/NPC_validator.time "$cli/solana-test-validator" \
  --ledger keys/NPC_ledger --limit-ledger-size 1000000 --bind-address 127.0.0.1 --rpc-port 18997 --faucet-port 19997 \
  --url https://api.devnet.solana.com --clone-feature-set \
  --clone-upgradeable-program 9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q \
  --clone-upgradeable-program 3jEFrv5Npn3RmFMW1Cbzq5yEiLdeFB5vbBGmnfoqK9vN \
  --clone-upgradeable-program CSnhzGdHQuzMW512CSunJzHrutcmh8ZAFzqx2z1zKorQ \
  --upgradeable-program BmsNikL97uF7bb1hMnJxsas7a9LjjK8vvT5Q1b7W34Qs pool.so Xjb7roDVPDSPoZpUmDVUW5SMx21x7oQEg16dhb5TDXD \
  --account "$payer" NPC_payer-genesis.json --quiet
