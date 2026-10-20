#!/usr/bin/env bash
set -euo pipefail
while systemctl --user is-active --quiet cx-devnet3-deploy-fresh.scope; do sleep 5; done
[[ $(cat receipts/deploy-fresh-run/exit.txt) == 0 ]]
[[ $(cat receipts/mint-run/exit.txt) == 0 ]]
exec python3 r1_devnet_spend.py r1-devnet.template.json receipts/spend
