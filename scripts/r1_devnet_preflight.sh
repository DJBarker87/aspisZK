#!/usr/bin/env bash
# Read-only resumption aid. Does not sign, airdrop, deploy, prove or submit.
set -euo pipefail
[[ $# == 2 ]] || { echo "usage: $0 config.json NEW_RECEIPT_DIR" >&2; exit 2; }
config=$1
out=$2
for command_name in jq curl sha256sum date; do
  command -v "$command_name" >/dev/null
done
jq -e '
  .schema == "aspis.r1.devnet-preflight-config.v1" and
  (.rpc_url | type == "string" and startswith("https://")) and
  ([.payer,.programs.verifier,.programs.pool,.programs.registry] |
    all(type == "string" and test("^[1-9A-HJ-NP-Za-km-z]{32,44}$"))) and
  ([.artifacts.verifier,.artifacts.pool,.artifacts.registry] |
    all(type == "string" and startswith("/")))
' "$config" >/dev/null
[[ ! -e "$out" ]] || { echo "refusing to overwrite receipts: $out" >&2; exit 2; }
mkdir -p "$out"
cp "$config" "$out/config.json"
rpc_url=$(jq -er .rpc_url "$config")
date -u +%FT%TZ >"$out/started-utc.txt"

# One request per named receipt; preserve HTTP errors and JSON-RPC errors.
# A read-only failure ends this run. Reruns must use a new receipt directory.
rpc() {
  local name=$1 method=$2 params=$3 result=0
  jq -nc --arg method "$method" --argjson params "$params" \
    '{jsonrpc:"2.0",id:1,method:$method,params:$params}' >"$out/$name.request.json"
  curl --fail-with-body --silent --show-error --max-time 45 \
    -H 'content-type: application/json' --data-binary @"$out/$name.request.json" \
    --output "$out/$name.json" --write-out '%{http_code} %{time_total}\n' \
    "$rpc_url" >"$out/$name.http-time.txt" 2>"$out/$name.stderr" || result=$?
  echo "$result" >"$out/$name.exit.txt"
  [[ $result == 0 ]] && jq -e '.error == null and has("result")' "$out/$name.json" >/dev/null
}

rpc genesis getGenesisHash '[]'
jq -e '.result == "EtWTRABZaYq6iMfeYKouRu166VU2xqa1wcaWoxPkrZBG"' \
  "$out/genesis.json" >/dev/null || { echo "devnet genesis mismatch" >&2; exit 3; }
rpc version getVersion '[]'
rpc slot getSlot '[{"commitment":"finalized"}]'
rpc feature getAccountInfo '["txv1aq4pp281K9um3tnPgkfX8UqtFT6wcVW3hNezGLL",{"encoding":"base64","commitment":"finalized"}]'
params=$(jq -c '[ [.payer,.programs.verifier,.programs.pool,.programs.registry,
  "5PjDJaGfSPJj4tFzMRCiuuAasKg5n8dJKXKenhuwZexx",
  "5bV6jUfhDHCQVA1WfKBUnXUsboJgoKgkzkKcxr3joew5"],
  {encoding:"base64",commitment:"finalized"} ]' "$config")
rpc accounts getMultipleAccounts "$params"

artifact_ok=true
for role in verifier pool registry; do
  case "$role" in
    verifier) expected=8cf8d84ed0fe340a190b4f40a9f953f0e0523370299ba3ec8bbed9d65b88ace3 ;;
    pool) expected=121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548 ;;
    registry) expected=7ad46f0d4b102a7c9699149d23bf6e065b6151feeaca95977d0a3146167d01ab ;;
  esac
  artifact=$(jq -er --arg role "$role" '.artifacts[$role]' "$config")
  if [[ -f "$artifact" ]]; then
    sha256sum "$artifact" >"$out/$role.sha256"
    read -r observed _ <"$out/$role.sha256"
    [[ "$observed" == "$expected" ]] || artifact_ok=false
  else
    echo "missing: $artifact" >"$out/$role.sha256"
    artifact_ok=false
  fi
done

jq -n --slurpfile config "$config" --slurpfile accounts "$out/accounts.json" \
  --argjson artifacts_match "$artifact_ok" \
  '{schema:"aspis.r1.devnet-preflight.v1",read_only:true,
    source_revision:"e90cf2f800f7177e5cca47aa7e5ba59a940130dd",
    payer_lamports:($accounts[0].result.value[0].lamports // 0),
    account_context_slot:$accounts[0].result.context.slot,
    account_order:["payer","verifier","pool","registry","audit_pool","audit_registry"],
    local_artifact_pins_match:$artifacts_match,
    configured_ids_match_pinned_verifier:(
      $config[0].programs.pool == "5PjDJaGfSPJj4tFzMRCiuuAasKg5n8dJKXKenhuwZexx" and
      $config[0].programs.registry == "5bV6jUfhDHCQVA1WfKBUnXUsboJgoKgkzkKcxr3joew5"),
    spend_ready:false,
    note:"Read-only observations only. No deployment, source refinement, upload carrier, registry policy, spend or negative test is validated by this script."}' \
  >"$out/summary.json"
cat "$out/summary.json"
date -u +%FT%TZ >"$out/finished-utc.txt"
# This preflight intentionally cannot certify a working spend implementation.
exit 4
