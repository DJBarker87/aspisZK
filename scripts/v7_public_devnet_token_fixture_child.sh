#!/usr/bin/env bash
set -euo pipefail

fail() { echo "FAIL: $*" >&2; exit 1; }

[[ $# -eq 1 ]] || fail "usage: $0 <new-evidence-dir>"
readonly EVIDENCE_DIR=$1
readonly RPC_URL=${ASPIS_TXV1_DISPOSABLE_RPC_URL:-}
readonly ACK=${ASPIS_TXV1_PUBLIC_DEVNET_MODE:-}
readonly BUILDER=${ASPIS_V7_PUBLIC_DEVNET_TOKEN_FIXTURE_BUILDER:-}
readonly PAYER_KEYPAIR=${ASPIS_TXV1_DISPOSABLE_PAYER_KEYPAIR:-}
readonly SOURCE_AUTHORITY_KEYPAIR=${ASPIS_TXV1_DISPOSABLE_SOURCE_AUTHORITY_KEYPAIR:-}
readonly MINT_KEYPAIR=${ASPIS_V7_PUBLIC_DEVNET_MINT_KEYPAIR:-}
readonly SOURCE_TOKEN_KEYPAIR=${ASPIS_V7_PUBLIC_DEVNET_SOURCE_TOKEN_KEYPAIR:-}
readonly DESTINATION_TOKEN_KEYPAIR=${ASPIS_V7_PUBLIC_DEVNET_DESTINATION_TOKEN_KEYPAIR:-}
readonly DEVNET_GENESIS_HASH=EtWTRABZaYq6iMfeYKouRu166VU2xqa1wcaWoxPkrZBG
readonly TOKEN_PROGRAM=TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA
readonly TXV1_FEATURE=txv1aq4pp281K9um3tnPgkfX8UqtFT6wcVW3hNezGLL

[[ "$ACK" == I_ACKNOWLEDGE_PUBLIC_DEVNET_TEST_ONLY ]] || fail "explicit public-devnet acknowledgement required"
[[ "$RPC_URL" == https://api.devnet.solana.com ]] || fail "canonical devnet RPC required"
[[ -x "$BUILDER" ]] || fail "token fixture builder missing"
for keypair in "$PAYER_KEYPAIR" "$SOURCE_AUTHORITY_KEYPAIR" "$MINT_KEYPAIR" \
  "$SOURCE_TOKEN_KEYPAIR" "$DESTINATION_TOKEN_KEYPAIR"; do
  [[ -f "$keypair" ]] || fail "task keypair missing"
done
[[ "$EVIDENCE_DIR" == /* && "$EVIDENCE_DIR" != / && ! -e "$EVIDENCE_DIR" ]] \
  || fail "evidence directory must be new, absolute, and non-root"
mkdir -p "$EVIDENCE_DIR"

rpc() {
  local response
  for _ in $(seq 1 30); do
    if response=$(curl --fail-with-body --silent --show-error --max-time 60 \
      -H 'content-type: application/json' --data-binary "$1" "$RPC_URL"); then
      printf '%s\n' "$response"
      return 0
    fi
    sleep 2
  done
  return 1
}

observed_genesis=$(rpc '{"jsonrpc":"2.0","id":1,"method":"getGenesisHash"}' | jq -er '.result')
[[ "$observed_genesis" == "$DEVNET_GENESIS_HASH" ]] || fail "devnet genesis mismatch"
feature=$(rpc "$(jq -nc --arg id "$TXV1_FEATURE" \
  '{jsonrpc:"2.0",id:2,method:"getAccountInfo",params:[$id,{encoding:"base64",commitment:"finalized"}]}')")
feature_tag=$(jq -er '.result.value.data[0]' <<<"$feature" | openssl base64 -d -A \
  | od -An -v -tu1 -N1 | tr -d '[:space:]')
[[ "$feature_tag" == 1 ]] || fail "TxV1 feature is not active"
slot=$(rpc '{"jsonrpc":"2.0","id":3,"method":"getSlot","params":[{"commitment":"finalized"}]}' | jq -er '.result')
blockhash=$(rpc "$(jq -nc --argjson slot "$slot" \
  '{jsonrpc:"2.0",id:4,method:"getLatestBlockhash",params:[{commitment:"finalized",minContextSlot:$slot}]}')" \
  | jq -er '.result.value.blockhash')
mint_rent=$(rpc '{"jsonrpc":"2.0","id":5,"method":"getMinimumBalanceForRentExemption","params":[82]}' | jq -er '.result')
token_rent=$(rpc '{"jsonrpc":"2.0","id":6,"method":"getMinimumBalanceForRentExemption","params":[165]}' | jq -er '.result')
jq -n --arg genesisHash "$observed_genesis" --arg payer "$PAYER_KEYPAIR" \
  --arg authority "$SOURCE_AUTHORITY_KEYPAIR" --arg mint "$MINT_KEYPAIR" \
  --arg source "$SOURCE_TOKEN_KEYPAIR" --arg destination "$DESTINATION_TOKEN_KEYPAIR" \
  --arg blockhash "$blockhash" --argjson slot "$slot" --argjson mintRent "$mint_rent" \
  --argjson tokenRent "$token_rent" \
  '{schema:"aspis.v7.public-devnet-token-fixture-input.v1",genesisHash:$genesisHash,
    payerKeypair:$payer,sourceAuthorityKeypair:$authority,mintKeypair:$mint,
    sourceTokenKeypair:$source,destinationTokenKeypair:$destination,recentBlockhash:$blockhash,
    minContextSlot:$slot,requestId:7000,mintRentLamports:$mintRent,
    tokenAccountRentLamports:$tokenRent,mintAmount:1000}' >"$EVIDENCE_DIR/input.json"
"$BUILDER" "$EVIDENCE_DIR/input.json" >"$EVIDENCE_DIR/signed-request.json"
jq -e '.schema == "aspis.v7.public-devnet-token-fixture-signed-request.v1" and
  .serializedTransactionBytes < 1232 and .mintAmount == 1000' \
  "$EVIDENCE_DIR/signed-request.json" >/dev/null || fail "invalid signed request"
simulation=$(rpc "$(jq -c '.simulationRequest' "$EVIDENCE_DIR/signed-request.json")")
jq . <<<"$simulation" >"$EVIDENCE_DIR/simulation.json"
jq -e '.error | not' <<<"$simulation" >/dev/null
jq -e '.result.value.err == null' <<<"$simulation" >/dev/null || fail "token fixture simulation failed"
send=$(rpc "$(jq -c '.sendRequest' "$EVIDENCE_DIR/signed-request.json")")
jq . <<<"$send" >"$EVIDENCE_DIR/send.json"
signature=$(jq -er '.result' <<<"$send")
[[ "$signature" == "$(jq -er '.signature' "$EVIDENCE_DIR/signed-request.json")" ]] \
  || fail "submitted token fixture wire changed"
finalized=false
for _ in $(seq 1 300); do
  status=$(rpc "$(jq -nc --arg signature "$signature" \
    '{jsonrpc:"2.0",id:8,method:"getSignatureStatuses",params:[[$signature],{searchTransactionHistory:true}]}')")
  if jq -e '.result.value[0] != null and .result.value[0].confirmationStatus == "finalized"' \
    <<<"$status" >/dev/null; then finalized=true; break; fi
  sleep 1
done
[[ "$finalized" == true ]] || fail "token fixture did not finalize"
rpc "$(jq -nc --arg signature "$signature" \
  '{jsonrpc:"2.0",id:9,method:"getTransaction",params:[$signature,{encoding:"json",commitment:"finalized",maxSupportedTransactionVersion:1}]}')" \
  | jq . >"$EVIDENCE_DIR/finalized-transaction.json"
jq -e '.result != null and .result.meta.err == null' "$EVIDENCE_DIR/finalized-transaction.json" >/dev/null \
  || fail "token fixture landed failure"
mapfile -t accounts < <(jq -r '.mint,.sourceTokenAccount,.destinationTokenAccount' "$EVIDENCE_DIR/signed-request.json")
rpc "$(jq -nc \
  '{jsonrpc:"2.0",id:10,method:"getMultipleAccounts",params:[$ARGS.positional,{encoding:"base64",commitment:"finalized"}]}' \
  --args "${accounts[@]}")" \
  | jq . >"$EVIDENCE_DIR/accounts.json"
jq -e --arg owner "$TOKEN_PROGRAM" '
  (.result.value | length) == 3 and all(.result.value[]; . != null and .owner == $owner)' \
  "$EVIDENCE_DIR/accounts.json" >/dev/null || fail "token account shape mismatch"
for spec in 0:82 1:165 2:165; do
  index=${spec%%:*}; expected=${spec#*:}
  actual=$(jq -er --argjson index "$index" '.result.value[$index].data[0]' \
    "$EVIDENCE_DIR/accounts.json" | openssl base64 -d -A | wc -c | tr -d '[:space:]')
  [[ "$actual" == "$expected" ]] || fail "token account data length mismatch"
done
jq -n --arg signature "$signature" \
  --argjson slot "$(jq -er '.result.slot' "$EVIDENCE_DIR/finalized-transaction.json")" \
  --arg mint "${accounts[0]}" --arg source "${accounts[1]}" --arg destination "${accounts[2]}" \
  --arg wireSha256 "$(jq -er '.signedWireSha256' "$EVIDENCE_DIR/signed-request.json")" \
  --argjson bytes "$(jq -er '.serializedTransactionBytes' "$EVIDENCE_DIR/signed-request.json")" \
  --argjson simulatedCu "$(jq -er '.result.value.unitsConsumed' "$EVIDENCE_DIR/simulation.json")" \
  --argjson landedCu "$(jq -er '.result.meta.computeUnitsConsumed' "$EVIDENCE_DIR/finalized-transaction.json")" \
  '{schema:"aspis.v7.public-devnet-token-fixture-finalized.v1",signature:$signature,slot:$slot,
    mint:$mint,sourceTokenAccount:$source,destinationTokenAccount:$destination,
    serializedTransactionBytes:$bytes,signedWireSha256:$wireSha256,
    simulatedCu:$simulatedCu,landedCu:$landedCu,submittedByteIdentically:true,finalized:true,
    publicDevnetTestOnly:true,mainnetReady:false}' >"$EVIDENCE_DIR/finalized.json"
