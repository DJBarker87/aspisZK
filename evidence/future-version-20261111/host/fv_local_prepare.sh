#!/bin/bash
# One-transaction rehearsal on a local validator: throwaway keys and the payer's genesis account
# (funded with exactly the devnet payer's balance on 2026-11-11, 10,811,659,736 lamports, so the
# rehearsal also checks that the balance is enough). Usage: fv_local_prepare.sh <name>
set -euo pipefail
W=/home/dombarker/project-offloads/future-version-20261111
L=$W/$1; CLI=/home/dombarker/project-offloads/codex-cx-devnet-rehearse-20261029/NDZ_runtime/extracted/solana-release/bin
test ! -e $L || { echo "exists: $L"; exit 2; }
mkdir -p -m 700 $L $L/keys $L/out
for k in payer verifier buffer; do $CLI/solana-keygen new --no-bip39-passphrase --silent -o $L/keys/$k.json; chmod 600 $L/keys/$k.json; done
python3 - "$($CLI/solana-keygen pubkey $L/keys/payer.json)" "$L" <<'PY'
import json,sys
json.dump({'pubkey':sys.argv[1],'account':{'lamports':10811659736,'data':['','base64'],'owner':'11111111111111111111111111111111','executable':False,'rentEpoch':0,'space':0}},open(sys.argv[2]+'/payer-genesis.json','w'))
PY
echo prepared $L
