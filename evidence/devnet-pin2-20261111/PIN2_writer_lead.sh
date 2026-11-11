#!/usr/bin/env bash
# Lead's copy of PIN2_writer.sh: same image class and caps; ROOT = zk-72's pin2-upload worktree (read-only), receipts under the lead's run dir.
set -euo pipefail
ROOT=/Users/dominic/ZK/.worktrees/pin2-upload
E=$ROOT/evidence/pin2-upload-20261110
F=$ROOT/evidence/devnet-frozen-20261109
R=/Users/dominic/aspis-lead-infra/pin2-run
PAYER=/Users/dominic/.config/solana/aspis-deploy/devnet-payer-20261029.json
KEYS=/Users/dominic/.config/solana/aspis-deploy/PIN2_upload-20261110
IMAGE=${PIN2_IMAGE:-aspis-pin2-writer:20261111}
[[ $# -gt 0 ]] || { echo 'Supply an explicit reviewed command.' >&2; exit 2; }
mkdir -p "$R/receipts"; mkdir -p -m 700 "$KEYS"
exec docker run --rm --platform linux/amd64 --memory 4g --memory-swap 4g \
  --cpus 4 --pids-limit 256 --user "$(id -u):$(id -g)" \
  --read-only --tmpfs /tmp:rw,size=64m --cap-drop ALL \
  --security-opt no-new-privileges -e NO_DNA=1 -e PYTHONDONTWRITEBYTECODE=1 \
  -e PYTHONPATH="$ROOT/scripts:$F/local:$E/devnet:$R/scripts" \
  --mount "type=bind,source=$ROOT,target=$ROOT,readonly" \
  --mount "type=bind,source=$R,target=$R" \
  --mount "type=bind,source=$PAYER,target=$PAYER,readonly" \
  --mount "type=bind,source=$KEYS,target=$KEYS" \
  -w "$ROOT" "$IMAGE" "$@"
