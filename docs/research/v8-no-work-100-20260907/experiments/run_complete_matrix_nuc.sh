#!/usr/bin/env bash
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)" rt="$(cd "$(dirname "$0")/../../../.." && pwd)"
[[ "$rt" == /home/dombarker/project-offloads/aspis-v8-* && ! -e "$rt/.git" ]] || exit 2
[[ $# == 2 && ( ! -e "$2" || "${ASPIS_COMPLETE_RESUME:-0}" == 1 ) ]] || { echo 'usage: script typed|hybrid|lazy|partial|v7|selected-v7 NEW_OUTPUT' >&2; exit 2; }
readonly mode="$1" out="$2"
case "$mode" in
 typed) verifier="$rt/sbf-complete/aspis_v8_complete_sbf.so"; matched=0;;
 hybrid) verifier="$rt/sbf-complete-hybrid/aspis_v8_complete_sbf.so"; matched=0;;
 lazy) verifier="$rt/sbf-complete-lazy/aspis_v8_complete_sbf.so"; matched=0;;
 partial) verifier="$rt/sbf-complete-partial/aspis_v8_complete_sbf.so"; matched=0;;
 channel) verifier="$rt/sbf-complete-channel/aspis_v8_complete_sbf.so"; matched=0;;
 group) verifier="$rt/sbf-complete-group/aspis_v8_complete_sbf.so"; matched=0;;
 suffix|tag7|scatter|tag-split|tag-bounded|tag-shared|tag-offset) verifier="$rt/sbf-complete-$mode/aspis_v8_complete_sbf.so"; matched=0;;
 v7) verifier="$rt/sbf-matched-v7/aspis_v8_complete_sbf.so"; matched=1;;
 selected-v7) verifier="$rt/sbf-selected-v7/aspis_verifier.so"; matched=1;;
 *) exit 2;;
esac
pool="$rt/sbf-matched-pool/aspis_v8_comparison_pool_sbf.so"; registry="$rt/sbf-matched-registry/aspis_v8_comparison_registry_sbf.so"
if [[ "${ASPIS_SELECTED_POOL:-0}" == 1 ]];then
 pool="$rt/sbf-selected-pool/aspis_pool.so";registry="$rt/sbf-selected-registry/aspis_registry.so"
fi
if [[ "${ASPIS_POOL_ZERO_FAST:-0}" == 1 ]];then
 pool="$rt/sbf-pool-zero-fast/aspis_pool.so";registry="$rt/sbf-selected-registry/aspis_registry.so"
fi
readonly double="$rt/sbf-complete/aspis_pair_forest_result_double.so"
readonly svm="$ex/performance-svm/target/release/aspis-v7-pair-forest-combined-rejection"
[[ -e "$out" ]] || mkdir "$out"
scope(){ local step="$1";shift;systemd-run --user --scope --unit="aspis-complete-$mode-$step-$(date +%s)-$$" -p MemoryHigh=3G -p MemoryMax=4G -p MemorySwapMax=0 /usr/bin/time -v env NO_DNA=1 ASPIS_MATCHED_V7="$matched" "$@"; }
for op in transfer withdrawal;do for count in 13 255;do
 seeds='1 2 3'
 if [[ "$matched" == 1 ]];then
  seeds=1
  case "$op-$count" in
   transfer-13) name=v7-pair-forest-transfer-strict-work-canonical-fixed.bin;;
   transfer-255) name=transfer-rollover-strict-canonical.bin;;
   withdrawal-13) name=withdrawal-same-page-counter0-strict-canonical.bin;;
   withdrawal-255) name=withdrawal-rollover-counter0-strict-canonical.bin;;
  esac
 fi
 for seed in $seeds;do
  if [[ "$matched" == 1 ]];then proof="$rt/complete-v7-inputs/$name";
  elif [[ "$op" == transfer ]];then proof="$rt/complete-transfer-$count-v1/proofs/proof-$seed.bin";
  else proof="$rt/complete-withdrawal-$count-v2/proofs/proof-$seed.bin";fi
  if [[ "${ASPIS_COMPLETE_MAX_FIXTURES:-0}" == 1 && "$matched" == 0 ]];then
   proof="$rt/complete-max-$op-$count-v1/proofs/proof-$seed.bin"
  fi
  for scenario in success proof-rejection wrong-release stale-lane replay;do
   [[ "$scenario" == success || "$seed" == 1 ]] || continue
   # The retained driver explicitly does not implement stale-lane rollover.
   [[ ( "$scenario" != stale-lane && "$scenario" != replay ) || "$count" != 255 ]] || continue
   if [[ -e "$out/$op-$count-$seed-$scenario.json" ]];then
    python3 - "$out/$op-$count-$seed-$scenario.json" "$verifier" "$proof" <<'PY'
import json,sys,hashlib
x=json.load(open(sys.argv[1]))
assert x["artifacts"]["selected_verifier"]["sha256"]==hashlib.sha256(open(sys.argv[2],"rb").read()).hexdigest()
assert x["fixture"]["external_path"]==sys.argv[3]
print("Preserving already completed evidence:",sys.argv[1])
PY
    continue
   fi
   scope "$op-$count-$seed-$scenario" "$svm" "$pool" "$verifier" "$registry" "$double" "$out/$op-$count-$seed-$scenario.json" "$proof" "$scenario" 1400000 asq8 "$count" "$op" 2>&1 | tee "$out/$op-$count-$seed-$scenario.log"
  done
 done
done;done
sha256sum "$verifier" "$pool" "$registry" "$svm" > "$out/artifact-hashes.txt"
