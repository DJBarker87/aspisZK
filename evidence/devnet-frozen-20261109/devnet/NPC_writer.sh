#!/usr/bin/env bash
# NPC_: NDZ_writer.sh adapted (worktree, receipt dir, key dir, PYTHONPATH). Same pinned image and caps.
# Invoke only explicitly selected commands. This file never selects a write itself.
set -euo pipefail
ROOT=/Users/dominic/ZK/.worktrees/cx-devnet2
E=$ROOT/evidence/devnet-frozen-20261109
R=$E/devnet/NPC_devnet_receipts
PAYER=/Users/dominic/.config/solana/aspis-deploy/devnet-payer-20261029.json
KEYS=/Users/dominic/.config/solana/aspis-deploy/NPC_frozen-20261109
IMAGE=sha256:a5fd19592cef47ad41bf1891997e324febf21a442cc71fac4eaf77877d60562a
[[ $# -gt 0 ]] || { echo 'Supply an explicit reviewed command.' >&2; exit 2; }
mkdir -p "$R"
exec docker run --rm --platform linux/amd64 --memory 4g --memory-swap 4g \
  --cpus 4 --pids-limit 256 --user "$(id -u):$(id -g)" \
  --read-only --tmpfs /tmp:rw,size=64m --cap-drop ALL \
  --security-opt no-new-privileges -e NO_DNA=1 -e PYTHONDONTWRITEBYTECODE=1 \
  -e PYTHONPATH="$ROOT/scripts:$E/local:$E/devnet" \
  --mount "type=bind,source=$ROOT,target=$ROOT,readonly" \
  --mount "type=bind,source=$R,target=$R" \
  --mount "type=bind,source=$PAYER,target=$PAYER,readonly" \
  --mount "type=bind,source=$KEYS,target=$KEYS" \
  -w "$ROOT" "$IMAGE" "$@"
