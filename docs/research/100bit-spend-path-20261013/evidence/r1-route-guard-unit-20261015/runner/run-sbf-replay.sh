#!/usr/bin/env bash
set -euo pipefail
ulimit -c 0
w=/home/dombarker/project-offloads/aspis-r1-route-guard-3c79ec30f-20261015
src="$w/source"
bin="$w/bin-route-guard"
results="$w/results/route-guard-replay"
cache=/home/dombarker/project-offloads/aspis-100bit-field-parser-candidate-20261014/cargo-target-v152
sol=/home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin
build_sbf="$sol/cargo-build-sbf"
driver="$cache/release/pool_gate"
p3=/home/dombarker/project-offloads/aspis-100bit-path-20261013/results/100bit-path-20261013
pool="$p3/pool-input-artifacts/aspis_pool.so"
registry="$p3/pool-input-artifacts/aspis_registry.so"
wrapper=/home/dombarker/project-offloads/aspis-100bit-path-20261013/scripts/v8_state_only_cu_record.py
proof_root=/home/dombarker/project-offloads/aspis-r1-split10-run-20261015
export PATH="$sol:/home/dombarker/.cargo/bin:/usr/bin:/bin"
export CARGO_TARGET_DIR="$cache"
export CARGO_BUILD_JOBS=2
export ASPIS_SOURCE_REVISION=3c79ec30fa44f408c716bb345050c137e907fa67+lib.rs-36d36ee707f565df675db2ef7b2d27467f8b79bb99142c4b21d6fb7cc81910c9
mkdir -p "$results" "$bin"
# Verify full source snapshot and the narrow overlay before building.
(cd "$src" && sha256sum -c "$w/source-overlay.sha256" >/dev/null)
test "$(sha256sum "$src/programs/r1-cost-probe/src/lib.rs" | cut -d' ' -f1)" = 36d36ee707f565df675db2ef7b2d27467f8b79bb99142c4b21d6fb7cc81910c9
test "$(sha256sum "$src/programs/r1-cost-probe/src/r1_pool_adapter.rs" | cut -d' ' -f1)" = b2adab8610189a5031fc6f28a7cdeef12c01aa292423743cb4696aa3ee1590a4
test "$(sha256sum "$src/tools/r1-cost-probe/src/bin/pool_gate.rs" | cut -d' ' -f1)" = f8986a966a6b17340c84c8d6a3514eed061f25cba8f8d65433d458dc8f379406
test "$(sha256sum "$src/Cargo.lock" | cut -d' ' -f1)" = f93f8f524fdd707c7a3b7feade31d015c891264b6c8fbd8bff885249e19600ea
test "$(sha256sum "$driver" | cut -d' ' -f1)" = 9ba7074f21a758cb2d69d66d8323fb78c0f60a98c981efe1e9e2f7ca265fddeb
test "$(sha256sum "$pool" | cut -d' ' -f1)" = 0e94c98d28437f0b01dce546fdefaad21dc10772a4d46991c2a573d8129cd4f6
test "$(sha256sum "$registry" | cut -d' ' -f1)" = 0f14c7b74ec6cbe3b3f637b0f24c7e8cdc46fd09f5b2e495fd51ada16ad8f11b
test ! -e "$bin/aspis_r1_cost_probe_program.so"
# Build into a new artifact directory; retain any generated keypair/artifacts.
systemd-run --user --scope --quiet -p MemoryHigh=8G -p MemoryMax=10G -p MemorySwapMax=0 -p TasksMax=128 \
  /usr/bin/python3 "$wrapper" "$results/sbf-build" "$build_sbf" \
  --manifest-path "$src/programs/r1-cost-probe/Cargo.toml" --sbf-out-dir "$bin" \
  --features pool-adapter,private-leaf-salts --tools-version v1.52 --skip-tools-install --offline \
  -- --locked -j 2
test -s "$bin/aspis_r1_cost_probe_program.so"
elf_sha=$(sha256sum "$bin/aspis_r1_cost_probe_program.so" | cut -d' ' -f1)
printf 'new_program_elf=%s\n' "$elf_sha" > "$results/build-pin.txt"
printf 'platform_tools=v1.52\nfeatures=pool-adapter,private-leaf-salts\n' >> "$results/build-pin.txt"
run_case() {
  local label="$1" operation="$2" scenario="$3" pairs="$4" proof="$5" pub="$6" proofsha="$7" pubsha="$8"
  local stem="$results/$label-run" evidence="$results/$label-evidence.json" task="$w/$label-task"
  test "$(sha256sum "$proof" | cut -d' ' -f1)" = "$proofsha"
  test "$(sha256sum "$pub" | cut -d' ' -f1)" = "$pubsha"
  test ! -e "$stem.json" && test ! -e "$evidence" && test ! -e "$task"
  test "$(sha256sum "$driver" | cut -d' ' -f1)" = 9ba7074f21a758cb2d69d66d8323fb78c0f60a98c981efe1e9e2f7ca265fddeb
  systemd-run --user --scope --quiet -p MemoryHigh=8G -p MemoryMax=10G -p MemorySwapMax=0 -p TasksMax=128 \
    /usr/bin/time -v -o "$stem.outer.time.log" /usr/bin/python3 "$wrapper" "$stem" "$driver" \
    "$pool" "$bin/aspis_r1_cost_probe_program.so" "$registry" "$evidence" "$task" \
    "$operation" "$scenario" --pairs "$pairs" --tx-version v0 --reuse "$proof" "$pub"
}
run_case transfer-13-route-guard transfer success 13 \
  "$proof_root/transfer-13-split10-success-b-task/r1-s2-proof.bin" \
  "$proof_root/transfer-13-split10-success-b-task/r1-s2-public-asf8.bin" \
  86d4212e675b36ebd556ca2b08b1b5e554cae15e77dfcd74c93a6f419129ed7c f6bcd49446f1077d2c5ed4be940e91f0be444efc5ae83024ec0700b8c205c331
run_case transfer-255-route-guard transfer success 255 \
  "$proof_root/transfer-255-split10-task/r1-s2-proof.bin" \
  "$proof_root/transfer-255-split10-task/r1-s2-public-asf8.bin" \
  3d68309b72bf61f0cd36e02b49b4c7d3f8377df81dd7c9b24a25e44ba722908e e201be4a028d74258c5344e7395bfabf7568af4ee7df0ec0c7b695f02fbacb15
run_case withdrawal-255-route-guard withdrawal success 255 \
  "$proof_root/withdrawal-255-split10-task/r1-s2-proof.bin" \
  "$proof_root/withdrawal-255-split10-task/r1-s2-public-asf8.bin" \
  dd83a7260a3a619cbe712ec591574ac625c0a38980c4c81ff6d3b26f8e13b853 7c2c27e135fa537776fad1457047f6c86ec351d64a8f0c6053674d2c2631200a
run_case transfer-1023-route-guard transfer success 1023 \
  "$proof_root/transfer-1023-split10-task/r1-s2-proof.bin" \
  "$proof_root/transfer-1023-split10-task/r1-s2-public-asf8.bin" \
  8569435667420b36a980493477f8fef7ef47e7351122647cf3747054079d4d62 72f067d263af326b017284579f30e3da7c843c6cbb29f1c6df94c8afbb1f2172
run_case withdrawal-1023-route-guard withdrawal success 1023 \
  "$proof_root/withdrawal-1023-split10-task/r1-s2-proof.bin" \
  "$proof_root/withdrawal-1023-split10-task/r1-s2-public-asf8.bin" \
  7bab9c8b102e6527118c589c984ef2b575bb046f18eaab4dc9c2926ec27d36f2 456bcde525f9e6947d9fc326daf3c3e01c8871cc4bf3d9fae6ab816980cb8f48
run_case transfer-13-replay-route-guard transfer replay 13 \
  "$proof_root/transfer-13-split10-replay-task/r1-s2-proof.bin" \
  "$proof_root/transfer-13-split10-replay-task/r1-s2-public-asf8.bin" \
  86d4212e675b36ebd556ca2b08b1b5e554cae15e77dfcd74c93a6f419129ed7c f6bcd49446f1077d2c5ed4be940e91f0be444efc5ae83024ec0700b8c205c331
