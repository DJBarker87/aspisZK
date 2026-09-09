#!/usr/bin/env bash
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)" rt="$(cd "$(dirname "$0")/../../../.." && pwd)"
[[ "$rt" == /home/dombarker/project-offloads/aspis-v8-* && ! -e "$rt/.git" ]] || exit 2
[[ $# == 2 && ! -e "$2" ]] || exit 2
readonly mode="$1" log="$2"
export NO_DNA=1 PATH=/home/dombarker/.cargo/bin:/home/dombarker/.local/share/solana/install/active_release/bin:/usr/bin:/bin
cd "$rt"
scope(){ systemd-run --user --scope --unit="aspis-channel-$mode-$(date +%s)-$$" -p MemoryHigh=5G -p MemoryMax=7G -p MemorySwapMax=0 /usr/bin/time -v "$@"; }
case "$mode" in
prepare-group)
 [[ "$(sha256sum crates/aspis-core/src/field.rs | cut -d' ' -f1)" == 0d64ce75f067ab8d3207ea088612b46d43bf4898cae58d2424d9389f095a5397 ]] || exit 2
 git apply --check --unidiff-zero "$ex/qm-group-partial.patch"
 git apply --unidiff-zero "$ex/qm-group-partial.patch"
 sha256sum crates/aspis-core/src/field.rs | tee "$log";;
prepare)
 [[ "$(sha256sum crates/aspis-core/src/field.rs | cut -d' ' -f1)" == 4233620fc2640a7fee834adacedfbf22e085efa6e314a550d2b39c361f15b13f ]] || exit 2
 git apply --check --recount "$ex/qm-channel-partial.patch"
 git apply --recount "$ex/qm-channel-partial.patch"
 sha256sum crates/aspis-core/src/field.rs | tee "$log";;
test|test-group)
 extra=();[[ "$mode" != test-group ]] || extra=(--cfg v8_qm_group_partial)
 scope rustc --edition 2021 -O -C overflow-checks=yes --cfg v8_range_m31 --cfg v8_range_cm31 --cfg v8_range_dots --cfg v8_cm_schoolbook --cfg v8_prepared_schoolbook --cfg v8_qm_hybrid --cfg v8_qm_lazy_c0 --cfg v8_qm_channel_partial "${extra[@]}" --test "$ex/range_kernel_controls.rs" -o "$rt/channel-$mode" 2>&1 | tee "$log"
 scope "$rt/channel-$mode" --test-threads 1 2>&1 | tee -a "$log";;
*) exit 2;;
esac
