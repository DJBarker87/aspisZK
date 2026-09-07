#!/usr/bin/env bash
set -euo pipefail

fail() { echo "FAIL: $*" >&2; exit 1; }

[[ $# -eq 1 ]] || fail "usage: $0 <new-evidence-dir>"
readonly EVIDENCE_DIR=$1
readonly RPC_URL=${ASPIS_TXV1_DISPOSABLE_RPC_URL:-}
readonly ACK=${ASPIS_TXV1_PUBLIC_DEVNET_MODE:-}
readonly BUILDER=${ASPIS_V7_PUBLIC_DEVNET_REGISTRY_BUILDER:-}
readonly PAYER_KEYPAIR=${ASPIS_TXV1_DISPOSABLE_PAYER_KEYPAIR:-}
readonly AUTHORITY_KEYPAIR=${ASPIS_V7_REGISTRY_AUTHORITY_KEYPAIR:-}
readonly REGISTRY_PROGRAM=${ASPIS_V7_REGISTRY_PROGRAM:-}
readonly POOL=${ASPIS_V7_POOL_MASTER:-}
readonly VERIFIER_PROGRAM=${ASPIS_V7_VERIFIER_PROGRAM:-}
readonly REGISTRY_SHA=${ASPIS_V7_REGISTRY_EXECUTABLE_SHA256:-}
readonly VERIFIER_SHA=${ASPIS_V7_VERIFIER_EXECUTABLE_SHA256:-}
readonly POLICY_BINDING=${ASPIS_V7_POLICY_BINDING_HEX:-}
readonly START_ACTION=${ASPIS_V7_REGISTRY_START_ACTION:-initialize}
readonly DEVNET_GENESIS_HASH=EtWTRABZaYq6iMfeYKouRu166VU2xqa1wcaWoxPkrZBG
readonly TXV1_FEATURE=txv1aq4pp281K9um3tnPgkfX8UqtFT6wcVW3hNezGLL

[[ "$ACK" == I_ACKNOWLEDGE_PUBLIC_DEVNET_TEST_ONLY ]] || fail "explicit public-devnet acknowledgement required"
[[ "$RPC_URL" == https://api.devnet.solana.com ]] || fail "canonical devnet RPC required"
[[ -x "$BUILDER" && -f "$PAYER_KEYPAIR" && -f "$AUTHORITY_KEYPAIR" ]] || fail "builder or task keypair missing"
[[ "$EVIDENCE_DIR" == /* && "$EVIDENCE_DIR" != / && ! -e "$EVIDENCE_DIR" ]] || fail "evidence directory must be new, absolute, and non-root"
[[ "$REGISTRY_SHA" =~ ^[0-9a-f]{64}$ && "$VERIFIER_SHA" =~ ^[0-9a-f]{64}$ && "$POLICY_BINDING" =~ ^[0-9a-f]{64}$ ]] || fail "invalid binding digest"
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
feature=$(rpc "$(jq -nc --arg id "$TXV1_FEATURE" '{jsonrpc:"2.0",id:2,method:"getAccountInfo",params:[$id,{encoding:"base64",commitment:"finalized"}]}')")
feature_tag=$(jq -er '.result.value.data[0]' <<<"$feature" | openssl base64 -d -A | od -An -v -tu1 -N1 | tr -d '[:space:]')
[[ "$feature_tag" == 1 ]] || fail "TxV1 feature is not active"

case "$START_ACTION" in
  initialize) actions=(initialize schedule activate freeze) ;;
  schedule) actions=(schedule activate freeze) ;;
  activate) actions=(activate freeze) ;;
  freeze) actions=(freeze) ;;
  *) fail "invalid Registry resume action" ;;
esac
for action in "${actions[@]}"; do
  action_dir="$EVIDENCE_DIR/$action"
  mkdir "$action_dir"
  slot=$(rpc '{"jsonrpc":"2.0","id":10,"method":"getSlot","params":[{"commitment":"finalized"}]}' | jq -er '.result')
  blockhash=$(rpc "$(jq -nc --argjson slot "$slot" '{jsonrpc:"2.0",id:11,method:"getLatestBlockhash",params:[{commitment:"finalized",minContextSlot:$slot}]}')" | jq -er '.result.value.blockhash')
  if [[ "$action" == schedule ]]; then
    processed_slot=$(rpc '{"jsonrpc":"2.0","id":12,"method":"getSlot","params":[{"commitment":"processed"}]}' | jq -er '.result')
    activation_slot=$((processed_slot + 50))
    activation_args=(--argjson activationSlot "$activation_slot")
  else
    activation_args=(--argjson activationSlot null)
  fi
  jq -n --arg action "$action" --arg genesisHash "$observed_genesis" \
    --arg registryProgram "$REGISTRY_PROGRAM" --arg pool "$POOL" \
    --arg verifierProgram "$VERIFIER_PROGRAM" --arg registrySha "$REGISTRY_SHA" \
    --arg verifierSha "$VERIFIER_SHA" --arg policyBinding "$POLICY_BINDING" \
    --arg payer "$PAYER_KEYPAIR" --arg authority "$AUTHORITY_KEYPAIR" \
    --arg blockhash "$blockhash" --argjson slot "$slot" "${activation_args[@]}" \
    '{schema:"aspis.v7.public-devnet-registry-input.v1",action:$action,genesisHash:$genesisHash,
      registryProgram:$registryProgram,pool:$pool,verifierProgram:$verifierProgram,
      registryExecutableSha256:$registrySha,verifierExecutableSha256:$verifierSha,
      policyBindingHex:$policyBinding,payerKeypair:$payer,authorityKeypair:$authority,
      recentBlockhash:$blockhash,minContextSlot:$slot,requestId:(1000+$slot),activationSlot:$activationSlot}' \
    >"$action_dir/input.json"
  "$BUILDER" "$action_dir/input.json" >"$action_dir/signed-request.json"
  simulation=$(rpc "$(jq -c '.simulationRequest' "$action_dir/signed-request.json")")
  jq . <<<"$simulation" >"$action_dir/simulation.json"
  jq -e '.error | not' <<<"$simulation" >/dev/null
  jq -e '.result.value.err == null' <<<"$simulation" >/dev/null || fail "$action simulation failed"
  send=$(rpc "$(jq -c '.sendRequest' "$action_dir/signed-request.json")")
  jq . <<<"$send" >"$action_dir/send.json"
  signature=$(jq -er '.result' <<<"$send")
  [[ "$signature" == "$(jq -er '.signature' "$action_dir/signed-request.json")" ]] || fail "$action wire changed"
  finalized=false
  for _ in $(seq 1 300); do
    status=$(rpc "$(jq -nc --arg signature "$signature" '{jsonrpc:"2.0",id:20,method:"getSignatureStatuses",params:[[$signature],{searchTransactionHistory:true}]}')")
    if jq -e '.result.value[0] != null and .result.value[0].confirmationStatus == "finalized"' <<<"$status" >/dev/null; then finalized=true; break; fi
    sleep 1
  done
  [[ "$finalized" == true ]] || fail "$action did not finalize"
  rpc "$(jq -nc --arg signature "$signature" '{jsonrpc:"2.0",id:21,method:"getTransaction",params:[$signature,{encoding:"json",commitment:"finalized",maxSupportedTransactionVersion:1}]}')" | jq . >"$action_dir/finalized-transaction.json"
  jq -e '.result != null and .result.meta.err == null' "$action_dir/finalized-transaction.json" >/dev/null || fail "$action landed failure"
  if [[ "$action" == schedule ]]; then
    activation_reached=false
    for _ in $(seq 1 180); do
      finalized_slot=$(rpc '{"jsonrpc":"2.0","id":22,"method":"getSlot","params":[{"commitment":"finalized"}]}' | jq -er '.result')
      if ((finalized_slot >= activation_slot)); then activation_reached=true; break; fi
      sleep 1
    done
    [[ "$activation_reached" == true ]] || fail "scheduled activation slot was not finalized"
  fi
done

registry=$(jq -er '.registryAccount' "$EVIDENCE_DIR/freeze/signed-request.json")
entry=$(jq -er '.entryAccount' "$EVIDENCE_DIR/freeze/signed-request.json")
for spec in "registry:$registry" "entry:$entry"; do
  name=${spec%%:*}; address=${spec#*:}
  rpc "$(jq -nc --arg address "$address" '{jsonrpc:"2.0",id:30,method:"getAccountInfo",params:[$address,{encoding:"base64",commitment:"finalized"}]}')" | jq . >"$EVIDENCE_DIR/$name-account.json"
  jq -e --arg owner "$REGISTRY_PROGRAM" '.result.value != null and .result.value.owner == $owner and .result.value.executable == false' "$EVIDENCE_DIR/$name-account.json" >/dev/null || fail "$name account shape mismatch"
done
jq -n --arg registry "$registry" --arg entry "$entry" \
  --arg registrySha "$(jq -er '.result.value.data[0]' "$EVIDENCE_DIR/registry-account.json" | openssl base64 -d -A | shasum -a 256 | awk '{print $1}')" \
  --arg entrySha "$(jq -er '.result.value.data[0]' "$EVIDENCE_DIR/entry-account.json" | openssl base64 -d -A | shasum -a 256 | awk '{print $1}')" \
  '{schema:"aspis.v7.public-devnet-registry-finalized.v1",registryAccount:$registry,entryAccount:$entry,
    accountDataSha256:{registry:$registrySha,entry:$entrySha},allSimulatedBeforeSubmission:true,
    allSubmittedByteIdentically:true,allFinalized:true,publicDevnetTestOnly:true,mainnetReady:false}' >"$EVIDENCE_DIR/finalized.json"
