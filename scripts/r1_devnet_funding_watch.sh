#!/usr/bin/env bash
# Public devnet only; retain all keys. One receipt per RPC attempt.
set -euo pipefail
[[ $# == 2 ]] || { echo "usage: $0 config.json NEW_RECEIPT_DIR" >&2; exit 2; }
config=$1 out=$2
[[ ! -e "$out" ]] || exit 2
mkdir -p "$out"
cp "$config" "$out/config.json"
rpc_url=$(jq -er '.rpc_url | select(. == "https://api.devnet.solana.com")' "$config")
payer=$(jq -er .payer "$config")
started=$(date +%s)
deadline=$((started + 8 * 60 * 60))
next_airdrop=$started
rpc() {
  local name=$1 method=$2 params=$3 status=0
  date -u +%FT%TZ >"$out/$name.started"
  jq -nc --arg method "$method" --argjson params "$params" \
    '{jsonrpc:"2.0",id:1,method:$method,params:$params}' >"$out/$name.request.json"
  /usr/bin/time -v -o "$out/$name.time" \
    curl --fail-with-body --silent --show-error --max-time 45 \
    -H 'content-type: application/json' --data-binary @"$out/$name.request.json" \
    --output "$out/$name.json" --write-out '%{http_code} %{time_total}\n' \
    "$rpc_url" >"$out/$name.http-time" 2>"$out/$name.stderr" || status=$?
  echo "$status" >"$out/$name.exit"
}
rpc genesis getGenesisHash '[]'
jq -e '.result == "EtWTRABZaYq6iMfeYKouRu166VU2xqa1wcaWoxPkrZBG"' "$out/genesis.json" >/dev/null
i=0
while :; do
  name=$(printf 'balance-%03d' "$i")
  rpc "$name" getBalance "[\"$payer\",{\"commitment\":\"finalized\"}]"
  if jq -e '.error == null and .result.value >= 3000000000' "$out/$name.json" >/dev/null 2>&1; then
    date -u +%FT%TZ >"$out/FUNDED"
    exit 0
  fi
  now=$(date +%s)
  if (( now >= deadline )); then
    date -u +%FT%TZ >"$out/TIMEOUT"
    exit 4
  fi
  if (( now >= next_airdrop )); then
    rpc "airdrop-$(printf '%03d' "$i")" requestAirdrop "[\"$payer\",1000000000,{\"commitment\":\"finalized\"}]"
    next_airdrop=$((now + 3600))
  fi
  i=$((i + 1))
  # Schedule balance observations five minutes apart, including RPC duration.
  next_poll=$((started + i * 300))
  now=$(date +%s)
  if (( next_poll > now )); then sleep "$((next_poll - now))"; fi
done
