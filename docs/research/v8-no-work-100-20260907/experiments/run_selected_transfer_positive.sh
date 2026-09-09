#!/usr/bin/env bash
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)"
readonly repo="$(git -C "$ex" rev-parse --show-toplevel)"
readonly cache=/Users/dominic/ZK/AspisFormal
readonly pin=bc945367d6b0d9a5b4cb2dc5a9ecad8ddcfb33ee
[[ $# == 1 && ! -e "$1" ]] || exit 2
readonly log="$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"
check(){ [[ "$(shasum -a 256 "$1" | cut -d' ' -f1)" == "$2" ]] || exit 2; }
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
    -M7000 -R "$ex" -o "$ex/SelectedTransferPositive.olean" "$ex/SelectedTransferPositive.lean" & pid=$!
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
  printf 'RESEARCH_PIN=%s\n' "$pin"
  git -C "$repo" rev-parse HEAD
  /Users/dominic/.elan/bin/lake env lean --version
  audit_imports AspisFormal.ArithmetizationCore
  shasum -a 256 "$ex/SelectedTransferPositive.lean" "$ex/SelectedPaymentRecovery.lean" "$ex/SelectedPaymentRecovery.olean"
  printf 'COMMAND=lean -M7000 -R %s -o %s %s\n' "$ex" \
    "$ex/SelectedTransferPositive.olean" "$ex/SelectedTransferPositive.lean"
  set +e; bounded_leaf; result=$?; set -e
  printf 'LEAN_EXIT=%s\n' "$result"
  [[ "$result" == 0 ]] || exit "$result"
  shasum -a 256 "$ex/SelectedTransferPositive.olean"
} 2>&1 | tee "$log"
