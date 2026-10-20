#!/usr/bin/env bash
set -euo pipefail
while systemctl --user is-active --quiet cx-devnet3-resume-buffer-small.scope; do sleep 5; done
[[ $(cat receipts/resume-buffer-small-run/exit.txt) == 0 ]]
exec python3 r1_devnet_deploy_paced.py r1-devnet.template.json receipts/deploy-paced verifier pool registry carrier
