#!/usr/bin/env bash
set -euo pipefail

fail() {
  echo "FAIL: $*" >&2
  exit 1
}

readonly ACK="I_ACKNOWLEDGE_LOCAL_ONLY_V7_CU_TAIL_PROBE"
[[ $# -eq 1 ]] || fail "usage: $0 <new-probe-evidence-dir>"
readonly EVIDENCE_DIR=$1
readonly RPC_URL=${ASPIS_TXV1_DISPOSABLE_RPC_URL:-}
readonly PAYER_KEYPAIR=${ASPIS_TXV1_DISPOSABLE_PAYER_KEYPAIR:-}
readonly AGAVE_BIN_DIR=${ASPIS_TXV1_DISPOSABLE_AGAVE_BIN_DIR:-}
readonly PROBE_BINARY=${ASPIS_V7_CU_TAIL_PROBE_BINARY:-}
readonly PROBE_BUILDER=${ASPIS_V7_CU_TAIL_PROBE_BUILDER:-}
readonly GENESIS_PROGRAM_ID=${ASPIS_TXV1_DISPOSABLE_CU_TAIL_PROBE_ID:-}

[[ "${ASPIS_V7_CU_TAIL_PROBE_ACK:-}" == "$ACK" ]] \
  || fail "missing exact local-only CU-tail-probe acknowledgement"
[[ "$RPC_URL" =~ ^http://127\.0\.0\.1:[0-9]+$ ]] || fail "disposable RPC is required"
[[ -f "$PAYER_KEYPAIR" ]] || fail "task-owned payer is unavailable"
[[ "$AGAVE_BIN_DIR" == /* && -x "$AGAVE_BIN_DIR/solana" && -x "$AGAVE_BIN_DIR/solana-keygen" ]] \
  || fail "absolute Agave binary directory is required"
[[ "$PROBE_BINARY" == /* && -f "$PROBE_BINARY" ]] || fail "absolute probe SBF is required"
[[ "$PROBE_BUILDER" == /* && -x "$PROBE_BUILDER" ]] || fail "prebuilt probe client is required"
[[ "$EVIDENCE_DIR" == /* && "$EVIDENCE_DIR" != / && ! -e "$EVIDENCE_DIR" ]] \
  || fail "evidence directory must be new, absolute and non-root"

for command_name in curl jq openssl seq shasum sort xargs; do
  command -v "$command_name" >/dev/null || fail "missing command: $command_name"
done

mkdir -p "$EVIDENCE_DIR/cases"
readonly WORK_DIR=$(mktemp -d "${TMPDIR:-/tmp}/aspis-v7-cu-tail-probe.XXXXXX")
cleanup() {
  case "$WORK_DIR" in
    */aspis-v7-cu-tail-probe.*) rm -rf -- "$WORK_DIR" ;;
    *) echo "refusing unexpected cleanup path: $WORK_DIR" >&2 ;;
  esac
}
trap cleanup EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

rpc() {
  curl --fail-with-body --silent --show-error --max-time 60 \
    -H 'content-type: application/json' --data-binary "$1" "$RPC_URL"
}

finalized_transaction() {
  local signature=$1 output=$2 request_id=$3 status finalized=false
  for _ in $(seq 1 600); do
    status=$(rpc "$(jq -nc --arg signature "$signature" --argjson id "$request_id" \
      '{jsonrpc:"2.0",id:$id,method:"getSignatureStatuses",params:[[$signature],{searchTransactionHistory:true}]}')")
    if jq -e '.result.value[0] != null and .result.value[0].confirmationStatus == "finalized"' \
      <<<"$status" >/dev/null; then
      finalized=true
      break
    fi
    sleep 0.1
  done
  [[ "$finalized" == true ]] || fail "probe transaction did not finalize: $signature"
  rpc "$(jq -nc --arg signature "$signature" --argjson id "$((request_id + 1))" \
    '{jsonrpc:"2.0",id:$id,method:"getTransaction",params:[$signature,{encoding:"json",commitment:"finalized",maxSupportedTransactionVersion:1}]}')" \
    | jq . >"$output"
}

# New sBPF-v0 deployment is deliberately disabled by the Agave 4.2 feature
# set, while existing v0 programs remain executable.  The preferred probe
# path therefore installs the fresh task-owned identity at disposable genesis.
# Runtime deployment can emit a temporary buffer recovery phrase on failure.
# This evidence path therefore requires genesis installation and never creates
# a runtime deployment buffer.
[[ -n "$GENESIS_PROGRAM_ID" ]] \
  || fail "CU-tail probe must be installed at disposable genesis"
readonly PROGRAM_ID="$GENESIS_PROGRAM_ID"
readonly DEPLOYMENT_MODE="disposable-genesis"
printf 'programId=%s\nmode=%s\n' "$PROGRAM_ID" "$DEPLOYMENT_MODE" \
  >"$EVIDENCE_DIR/deploy.log"

rpc "$(jq -nc --arg id "$PROGRAM_ID" \
  '{jsonrpc:"2.0",id:1,method:"getAccountInfo",params:[$id,{encoding:"base64",commitment:"finalized"}]}')" \
  | jq . >"$EVIDENCE_DIR/program-account.json"
jq -e '.result.value != null and .result.value.executable == true' \
  "$EVIDENCE_DIR/program-account.json" >/dev/null || fail "probe program is not executable"
NO_DNA=1 "$AGAVE_BIN_DIR/solana" program dump --url "$RPC_URL" "$PROGRAM_ID" \
  "$WORK_DIR/observed-probe.so" >"$EVIDENCE_DIR/program-dump.log"
readonly SOURCE_SHA=$(shasum -a 256 "$PROBE_BINARY" | awk '{print $1}')
readonly OBSERVED_SHA=$(shasum -a 256 "$WORK_DIR/observed-probe.so" | awk '{print $1}')
[[ "$SOURCE_SHA" == "$OBSERVED_SHA" ]] || fail "deployed probe binary hash mismatch"

slot=$(rpc '{"jsonrpc":"2.0","id":2,"method":"getSlot","params":[{"commitment":"finalized"}]}' | jq -er '.result')
blockhash=$(rpc "$(jq -nc --argjson slot "$slot" \
  '{jsonrpc:"2.0",id:3,method:"getLatestBlockhash",params:[{commitment:"finalized",minContextSlot:$slot}]}')" \
  | jq -er '.result.value.blockhash')
jq -n --arg ack "$ACK" --arg payer "$PAYER_KEYPAIR" --arg blockhash "$blockhash" \
  --arg programId "$PROGRAM_ID" --argjson slot "$slot" \
  '{schema:"aspis.v7.cu-tail-probe-input.v1",disposableAcknowledgement:$ack,
    payerKeypair:$payer,recentBlockhash:$blockhash,minContextSlot:$slot,
    requestId:1000,probeProgramId:$programId}' >"$WORK_DIR/input.json"
"$PROBE_BUILDER" "$WORK_DIR/input.json" >"$EVIDENCE_DIR/signed-requests.json"
jq -e '.schema == "aspis.v7.cu-tail-probe-signed-requests.v1" and .localOnly == true and
  (.requests | length) == 8 and all(.requests[];
    .serializedTransactionBytes < 1232 and (.signedWireSha256 | test("^[0-9a-f]{64}$")))' \
  "$EVIDENCE_DIR/signed-requests.json" >/dev/null || fail "probe signed requests are malformed"

for index in 0 1 2 3 4 5 6 7; do
  name=$(jq -er ".requests[$index].name" "$EVIDENCE_DIR/signed-requests.json")
  case_dir="$EVIDENCE_DIR/cases/$name"
  mkdir "$case_dir"
  simulation=$(rpc "$(jq -c ".requests[$index].simulationRequest" "$EVIDENCE_DIR/signed-requests.json")")
  jq . <<<"$simulation" >"$case_dir/simulation.json"
  jq -e '.error | not' <<<"$simulation" >/dev/null || fail "$name simulation RPC error"
  jq -e '.result.value.err == null and (.result.value.unitsConsumed | type == "number")' \
    <<<"$simulation" >/dev/null || fail "$name simulation failed"
  send=$(rpc "$(jq -c ".requests[$index].sendRequest" "$EVIDENCE_DIR/signed-requests.json")")
  jq . <<<"$send" >"$case_dir/send.json"
  signature=$(jq -er '.result' <<<"$send")
  [[ "$signature" == "$(jq -er ".requests[$index].signature" "$EVIDENCE_DIR/signed-requests.json")" ]] \
    || fail "$name submission was not byte-identical"
  finalized_transaction "$signature" "$case_dir/finalized-transaction.json" "$((2000 + index * 10))"
  jq -e '.result.meta.err == null and (.result.meta.computeUnitsConsumed | type == "number")' \
    "$case_dir/finalized-transaction.json" >/dev/null || fail "$name finalized execution failed"
  jq -n --arg name "$name" \
    --arg signature "$signature" \
    --arg hash "$(jq -er ".requests[$index].signedWireSha256" "$EVIDENCE_DIR/signed-requests.json")" \
    --argjson bytes "$(jq -er ".requests[$index].serializedTransactionBytes" "$EVIDENCE_DIR/signed-requests.json")" \
    --argjson simulationCu "$(jq -er '.result.value.unitsConsumed' "$case_dir/simulation.json")" \
    --argjson landedCu "$(jq -er '.result.meta.computeUnitsConsumed' "$case_dir/finalized-transaction.json")" \
    --argjson finalizedSlot "$(jq -er '.result.slot' "$case_dir/finalized-transaction.json")" \
    '{name:$name,serializedTransactionBytes:$bytes,signedWireSha256:$hash,
      simulationSubmissionWireIdentical:true,simulationCu:$simulationCu,
      landedCu:$landedCu,signature:$signature,finalizedSlot:$finalizedSlot}' \
    >"$case_dir/summary.json"
done

jq -n --arg programId "$PROGRAM_ID" --arg binarySha256 "$SOURCE_SHA" \
  --arg deploymentMode "$DEPLOYMENT_MODE" \
  --slurpfile min "$EVIDENCE_DIR/cases/qm31-minimum/summary.json" \
  --slurpfile max "$EVIDENCE_DIR/cases/qm31-maximum-successful/summary.json" \
  --slurpfile best "$EVIDENCE_DIR/cases/query-order-best/summary.json" \
  --slurpfile worst "$EVIDENCE_DIR/cases/query-order-worst/summary.json" \
  --slurpfile c0 "$EVIDENCE_DIR/cases/counter-zero/summary.json" \
  --slurpfile c20 "$EVIDENCE_DIR/cases/counter-twenty/summary.json" \
  --slurpfile f199 "$EVIDENCE_DIR/cases/frontier-199/summary.json" \
  --slurpfile f203 "$EVIDENCE_DIR/cases/frontier-203/summary.json" \
  '{schema:"aspis.v7.cu-tail-probe-evidence.v1",cluster:"disposable-local-validator",
    localOnly:true,probeProgramId:$programId,probeBinarySha256:$binarySha256,
    deploymentMode:$deploymentMode,
    cases:[$min[0],$max[0],$best[0],$worst[0],$c0[0],$c20[0],$f199[0],$f203[0]],
    landedDeltasCu:{qm31MaximumMinusMinimum:($max[0].landedCu-$min[0].landedCu),
      queryWorstMinusBest:($worst[0].landedCu-$best[0].landedCu),
      counterTwentyMinusZero:($c20[0].landedCu-$c0[0].landedCu),
      frontier203Minus199:($f203[0].landedCu-$f199[0].landedCu)},
    privateKeysCommitted:false,publicClusterTransaction:false,mainnetReady:false}' \
  >"$EVIDENCE_DIR/summary.json"

(
  cd "$EVIDENCE_DIR"
  find . -type f ! -name SHA256SUMS -print0 | sort -z | xargs -0 shasum -a 256 >SHA256SUMS
)
