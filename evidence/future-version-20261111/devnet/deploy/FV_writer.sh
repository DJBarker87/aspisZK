#!/usr/bin/env bash
# Future-version one-transaction devnet run: PIN2_writer_lead.sh with ROOT = the future-version
# worktree (read-only) and the image carrying the one-transaction client. Same caps.
set -euo pipefail
ROOT=/Users/dominic/ZK/.worktrees/future-version
D=$ROOT/evidence/future-version-20261111/devnet
R=/Users/dominic/aspis-lead-infra/fv-run
PAYER=/Users/dominic/.config/solana/aspis-deploy/devnet-payer-20261029.json
KEYS=/Users/dominic/.config/solana/aspis-deploy/FV_onetx-20261111
IMAGE=${FV_IMAGE:-aspis-fv-writer:20261111}
[[ $# -gt 0 ]] || { echo 'Supply an explicit reviewed command.' >&2; exit 2; }
exec docker run --rm --platform linux/amd64 --memory 4g --memory-swap 4g \
  --cpus 4 --pids-limit 256 --user "$(id -u):$(id -g)" \
  --read-only --tmpfs /tmp:rw,size=64m --cap-drop ALL \
  --security-opt no-new-privileges -e NO_DNA=1 -e PYTHONDONTWRITEBYTECODE=1 \
  -e PYTHONPATH="$ROOT/scripts:$ROOT/evidence/pin2-upload-20261110/devnet:$D" \
  --mount "type=bind,source=$ROOT,target=$ROOT,readonly" \
  --mount "type=bind,source=$R,target=$R" \
  --mount "type=bind,source=$PAYER,target=$PAYER,readonly" \
  --mount "type=bind,source=$KEYS,target=$KEYS" \
  -w "$ROOT" "$IMAGE" "$@"
