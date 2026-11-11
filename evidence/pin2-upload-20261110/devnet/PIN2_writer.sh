#!/usr/bin/env bash
# PIN2_: NPC_writer.sh adapted (root, receipt dir, key dir, PYTHONPATH). Same pinned image and caps.
# Invoke only explicitly selected commands, e.g.
#   PIN2_writer.sh python3 $E/devnet/PIN2_preflight.py $E/devnet/PIN2_devnet.json $R/PIN2_PREFLIGHT.json
#   PIN2_writer.sh python3 $E/devnet/PIN2_spend.py $E/devnet/PIN2_devnet.json $R/PIN2_spend > $R/PIN2_spend.log
#   PIN2_writer.sh python3 $E/devnet/PIN2_collect_devnet.py $E/devnet/PIN2_devnet.json $R
#   PIN2_writer.sh python3 $E/devnet/PIN2_recover.py $E/devnet/PIN2_devnet.json $R/PIN2_spend   (dry run; add --send)
# The image must carry a devnet_spend signer built from this branch (pin2_* planner actions).
# This file never selects a write itself.
set -euo pipefail
ROOT=${PIN2_ROOT:-/Users/dominic/ZK/.worktrees/pin2-upload}
E=$ROOT/evidence/pin2-upload-20261110
F=$ROOT/evidence/devnet-frozen-20261109
R=$E/devnet/PIN2_devnet_receipts
PAYER=/Users/dominic/.config/solana/aspis-deploy/devnet-payer-20261029.json
KEYS=/Users/dominic/.config/solana/aspis-deploy/PIN2_upload-20261110
IMAGE=${PIN2_IMAGE:-sha256:a5fd19592cef47ad41bf1891997e324febf21a442cc71fac4eaf77877d60562a}
[[ $# -gt 0 ]] || { echo 'Supply an explicit reviewed command.' >&2; exit 2; }
mkdir -p "$R"; mkdir -p -m 700 "$KEYS"
exec docker run --rm --platform linux/amd64 --memory 4g --memory-swap 4g \
  --cpus 4 --pids-limit 256 --user "$(id -u):$(id -g)" \
  --read-only --tmpfs /tmp:rw,size=64m --cap-drop ALL \
  --security-opt no-new-privileges -e NO_DNA=1 -e PYTHONDONTWRITEBYTECODE=1 \
  -e PYTHONPATH="$ROOT/scripts:$F/local:$E/devnet" \
  --mount "type=bind,source=$ROOT,target=$ROOT,readonly" \
  --mount "type=bind,source=$R,target=$R" \
  --mount "type=bind,source=$PAYER,target=$PAYER,readonly" \
  --mount "type=bind,source=$KEYS,target=$KEYS" \
  -w "$ROOT" "$IMAGE" "$@"
