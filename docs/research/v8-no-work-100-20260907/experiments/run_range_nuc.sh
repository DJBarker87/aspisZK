#!/usr/bin/env bash
# Research-only reproduction in a disposable, task-owned NUC source COPY.
set -euo pipefail
[[ $# == 3 && "$2" == /* && ! -e "$2" && -d "$3" ]] || {
  echo "usage: bash run_range_nuc.sh profiled|quiet NEW_OUTPUT EXISTING_FIXTURES" >&2; exit 2;
}
readonly mode="$1" range_out="$2" fixture_dir="$3"
readonly range_exp="$(cd "$(dirname "$0")" && pwd)"
readonly range_root="$(cd "$range_exp/../../../.." && pwd)"
[[ "$range_root" == /home/dombarker/project-offloads/aspis-v8-* && ! -e "$range_root/.git" ]] || {
  echo "Refusing to patch a repository/worktree or an unrecognised source copy" >&2; exit 2;
}
[[ "$mode" == profiled || "$mode" == quiet ]] || exit 2
readonly original=5795495e2fa9ad85e097c2ad96ffc826aaad3c16afc0e0bd00459f9f51068cd8
readonly patched=8f8b3aad6193ba5ee0b160a61994b19b5f154009ff250d704203c713bf38778c
read -r actual _ < <(sha256sum "$range_root/crates/aspis-core/src/field.rs")
if [[ "$actual" == "$original" ]]; then
  for patch in canonical-m31 canonical-cm31 canonical-dots canonical-cm-schoolbook canonical-branchless canonical-prepared; do
    (cd "$range_root" && git apply --check "$range_exp/$patch.patch" && git apply "$range_exp/$patch.patch")
  done
fi
read -r actual _ < <(sha256sum "$range_root/crates/aspis-core/src/field.rs")
[[ "$actual" == "$patched" ]] || { echo "Unexpected field source hash; preserve it and inspect manually" >&2; exit 2; }
# Branchless control is present behind an INACTIVE cfg, retained for falsifiability.
# Never use overflow-checks=off, a package override, or v8_branchless_m31 here.
flags="--cfg v8_performance_sbf --cfg v8_performance_fast --cfg v8_structured --cfg v8_fine_profile --cfg v8_batch_m --cfg v8_tower_batch --cfg v8_query_kernels --cfg v8_fused_rows --cfg v8_shared_weights --cfg v8_block_horner --cfg v8_gamma_wrap --cfg v8_reuse_gamma --cfg v8_grouped_linear --cfg v8_query_shared --cfg v8_range_m31 --cfg v8_range_cm31 --cfg v8_sparse_groups --cfg v8_range_dots --cfg v8_cm_schoolbook --cfg v8_prepared_schoolbook -A dead_code -A unexpected_cfgs"
[[ "$mode" != quiet ]] || flags+=" --cfg v8_quiet_profile"
readonly tools=/home/dombarker/.cache/solana/v1.54/platform-tools
readonly range_path=/home/dombarker/.cargo/bin:/home/dombarker/.local/share/solana/install/active_release/bin:/usr/bin:/bin
mkdir "$range_out"
readonly unit="aspis-v8-range-$mode-$(date +%s)-$$"
scope(){
  local part="$1"; shift
  systemd-run --user --scope --unit="$unit-$part" -p MemoryHigh=5G -p MemoryMax=7G -p MemorySwapMax=0 \
    /usr/bin/time -v env NO_DNA=1 PATH="$range_path" "$@"
}
scope field-build /home/dombarker/.cargo/bin/rustc --edition 2021 -O -C overflow-checks=yes \
 --cfg v8_range_m31 --cfg v8_range_cm31 --cfg v8_range_dots --cfg v8_cm_schoolbook --cfg v8_prepared_schoolbook \
 --test "$range_exp/range_kernel_controls.rs" -o "$range_out/field-tests" 2>&1 | tee "$range_out/field-build.log"
scope field-tests "$range_out/field-tests" --test-threads 1 2>&1 | tee "$range_out/field-tests.log"
scope sbf env RUSTC="$tools/rust/bin/rustc" RUSTFLAGS="$flags" cargo-build-sbf --offline \
 --skip-tools-install --no-rustup-override --tools-version v1.54 --jobs 2 --features selected-v7-kernels \
 --manifest-path "$range_exp/performance-sbf/Cargo.toml" --sbf-out-dir "$range_out/sbf" -- --locked \
 2>&1 | tee "$range_out/sbf-build.log"
if rg -q 'overflows the maximum allowed frame|Stack offset.*exceeded|Error:' "$range_out/sbf-build.log"; then
  echo "Inspect the exact emitted function before proceeding; no automatic warning waiver" >&2; exit 1
fi
"$tools/llvm/bin/llvm-objdump" --disassemble --demangle \
 "$range_exp/performance-sbf/target/sbpf-solana-solana/release/aspis_v8_performance_sbf.so" \
 | python3 "$range_exp/audit_range_stack.py" | tee "$range_out/stack.json"
scope driver cargo build --offline --locked --release --jobs 2 --manifest-path "$range_exp/performance-svm/Cargo.toml" \
 2>&1 | tee "$range_out/driver-build.log"
scope svm env ASPIS_V8_EXTENDED_REJECTIONS=1 "$range_exp/performance-svm/target/release/aspis-v8-performance-svm" \
 "$range_out/sbf/aspis_v8_performance_sbf.so" "$fixture_dir" 2>&1 | tee "$range_out/svm.log"
sha256sum "$range_out/sbf/aspis_v8_performance_sbf.so" "$range_root/crates/aspis-core/src/field.rs" \
 "$fixture_dir"/proof-{1,2,3}.bin "$range_exp"/{structured_weights,sparse_grouped,query_arithmetic,performance_verifier,performance}.rs \
 | tee "$range_out/hashes.txt"
