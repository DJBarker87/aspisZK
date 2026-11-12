#!/usr/bin/env bash
# Aspis freeze devnet run: the run scripts inside the capped container (FV_writer.sh of the earlier
# one-transaction run, with this run's directory, key directory and image). The repository is mounted
# read-only; the run scripts are the unchanged ones of evidence/future-version-20261111/devnet.
set -euo pipefail
ROOT=/Users/dominic/ZK/.worktrees/future-version
D=$ROOT/evidence/future-version-20261111/devnet
R=/Users/dominic/aspis-lead-infra/aspis-freeze-run
PAYER=/Users/dominic/.config/solana/aspis-deploy/devnet-payer-20261029.json
KEYS=/Users/dominic/.config/solana/aspis-deploy/ASPIS_onetx-20261112
IMAGE=${ASPIS_IMAGE:-aspis-freeze-writer:20261112}
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
