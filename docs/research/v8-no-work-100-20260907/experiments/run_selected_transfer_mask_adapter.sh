#!/usr/bin/env bash
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)"
readonly repo="$(git -C "$ex" rev-parse --show-toplevel)"
readonly cache=/Users/dominic/ZK/AspisFormal
readonly pin=33e13de4e4b8bfdef7f3f2fb2e472b34db44865e
[[ $# == 2 && ! -e "$2" ]] || exit 2
readonly mode="$1"
readonly log="$(cd "$(dirname "$2")" && pwd)/$(basename "$2")"
case "$mode" in
  export-mask) target=PaymentMaskRead; [[ ! -e "$ex/PaymentMaskRead.olean" ]] || exit 2;;
  leaf) target=SelectedTransferMaskAdapter; [[ -e "$ex/PaymentMaskRead.olean" ]] || exit 2;;
  *) exit 2;;
esac
readonly target
check(){ [[ "$(shasum -a 256 "$1" | cut -d' ' -f1)" == "$2" ]] || exit 2; }
check "$ex/PaymentMaskRead.lean" ca88ef28b6fa99fd9c52ebc92cbfdd951ff17a280adce0d6d8054fc7a4689c15
if [[ "$mode" == leaf ]]; then
  check "$ex/PaymentMaskRead.olean" f44d45e32240e9d4579813ceb427ce2cb938cb90dcfa00c47f9e1fad2c139803
fi
check "$ex/SelectedTransferPositive.lean" 00f427ff1d17f2b01a7fbb7f18a4bc68b9814d804a05242f0ac34a5d6a9ff48f
check "$ex/SelectedTransferPositive.olean" 775b0b9796a0b206c279209742bb6a9fdfceb73428f3fe7f5087702bea19b560
check "$ex/SelectedPaymentRecovery.lean" 4c8ba95e27ed5e50e1927b6e9233b9f387b8674f5ca059949f8cd04ca7a63c18
check "$ex/SelectedPaymentRecovery.olean" ee2166caaf0ff244add6113c14b19fd8622c00fbd87607b195063b42323e3ac0
check "$cache/.lake/build/lib/lean/AspisFormal/ArithmetizationCore.olean" 6ab5f3738e8018b86409fd1ec394527d1e6eded5816817f11385529e0c579300
check "$cache/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean" 9c5bf984a8c4ed7c7854d68673a37a3847ff24783554f451920d4ff95d68b97e
[[ "$(git -C "$cache/.lake/packages/mathlib" rev-parse HEAD)" == 81a5d257c8e410db227a6665ed08f64fea08e997 ]] || exit 2
seen=' '
audit_imports(){
  local module="$1" rel child
  case "$seen" in *" $module "*) return;; esac
  seen="$seen$module "; rel="${module//.//}"
  [[ "$(git -C "$repo" hash-object "AspisFormal/$rel.lean")" == \
     "$(git -C "$repo" rev-parse "$pin:AspisFormal/$rel.lean")" ]] || exit 2
  cmp "$repo/AspisFormal/$rel.lean" "$cache/$rel.lean"
  shasum -a 256 "$repo/AspisFormal/$rel.lean" "$cache/.lake/build/lib/lean/$rel.olean"
  while read -r child; do audit_imports "$child"; done < <(
    awk '$1=="import" && $2 ~ /^AspisFormal\./ {print $2}' "$repo/AspisFormal/$rel.lean")
}
bounded_leaf(){
  local leanpath pid rss ids child
  leanpath="$(/Users/dominic/.elan/bin/lake env printenv LEAN_PATH)"
  env LEAN_PATH="$ex:$leanpath" /usr/bin/time -l \
    /Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
    -M7000 -R "$ex" -o "$ex/$target.olean" "$ex/$target.lean" & pid=$!
  while kill -0 "$pid" 2>/dev/null; do
    rss="$(ps -axo pid=,ppid=,rss= | awk -v root="$pid" '
      {parent[$1]=$2;mem[$1]=$3} END {for(pid in parent){p=pid;
        for(n=0;n<64 && p!=0;n++){if(p==root){total+=mem[pid];break}p=parent[p]}}
        print total+0}')"
    if (( rss > 7340032 )); then
      printf 'AGGREGATE_RSS_STOP_KIB=%s\n' "$rss"
      ids="$(ps -axo pid=,ppid= | awk -v root="$pid" '
        {parent[$1]=$2} END {for(pid in parent){p=pid;for(n=0;n<64 && p!=0;n++){
          if(p==root && pid!=root){print pid;break}p=parent[p]}}}')"
      while read -r child; do [[ -z "$child" ]] || kill -TERM "$child" 2>/dev/null || true; done <<< "$ids"
      wait "$pid" || true; return 137
    fi
    sleep 1
  done
  wait "$pid"
}
cd "$cache"
{
  printf 'RESEARCH_PIN=%s\nMODE=%s\n' "$pin" "$mode"
  git -C "$repo" rev-parse HEAD
  /Users/dominic/.elan/bin/lake env lean --version
  audit_imports AspisFormal.ArithmetizationCore
  shasum -a 256 "$ex/$target.lean" "$ex/PaymentMaskRead.lean" \
    "$ex/SelectedTransferPositive.lean" "$ex/SelectedTransferPositive.olean"
  if [[ "$mode" == leaf ]]; then shasum -a 256 "$ex/PaymentMaskRead.olean"; fi
  printf 'COMMAND=lean -M7000 -R %s -o %s %s\n' "$ex" \
    "$ex/$target.olean" "$ex/$target.lean"
  set +e; bounded_leaf; result=$?; set -e
  printf 'LEAN_EXIT=%s\n' "$result"
  [[ "$result" == 0 ]] || exit "$result"
  shasum -a 256 "$ex/$target.olean"
} 2>&1 | tee "$log"
