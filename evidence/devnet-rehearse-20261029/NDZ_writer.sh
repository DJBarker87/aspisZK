#!/usr/bin/env bash
# Invoke only explicitly selected commands. This file never selects a write itself.
set -euo pipefail
ROOT=/Users/dominic/ZK/.worktrees/cx-devnet-rehearse
E=$ROOT/evidence/devnet-rehearse-20261029
PAYER=/Users/dominic/.config/solana/aspis-deploy/devnet-payer-20261029.json
KEYS=/Users/dominic/.config/solana/aspis-deploy/NDZ_release-20261029
IMAGE=sha256:a5fd19592cef47ad41bf1891997e324febf21a442cc71fac4eaf77877d60562a
[[ $# -gt 0 ]] || { echo 'Supply an explicit reviewed command.' >&2; exit 2; }
mkdir -p "$E/NDZ_devnet_receipts"
exec docker run --rm --platform linux/amd64 --memory 4g --memory-swap 4g \
  --cpus 4 --pids-limit 256 --user "$(id -u):$(id -g)" \
  --read-only --tmpfs /tmp:rw,size=64m --cap-drop ALL \
  --security-opt no-new-privileges -e NO_DNA=1 \
  --mount "type=bind,source=$ROOT,target=$ROOT,readonly" \
  --mount "type=bind,source=$E/NDZ_devnet_receipts,target=$E/NDZ_devnet_receipts" \
  --mount "type=bind,source=$PAYER,target=$PAYER,readonly" \
  --mount "type=bind,source=$KEYS,target=$KEYS" \
  -w "$ROOT" "$IMAGE" "$@"
