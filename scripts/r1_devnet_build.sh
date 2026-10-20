#!/usr/bin/env bash
# Run on the Linux build host inside the required capped systemd scope.
set -euo pipefail
[[ $# == 3 ]] || { echo "usage: $0 HOST_TASK_DIR default|devnet SOURCE_REVISION" >&2; exit 2; }
task=$1 mode=$2 revision=$3
[[ $mode == default || $mode == devnet ]] || exit 2
out=$task/receipts/build-$mode
[[ ! -e "$out" ]] || exit 2
mkdir -p "$out" "$task/artifacts/$mode"
printf '%s\n' "$revision" >"$out/source-revision.txt"
date -u +%FT%TZ >"$out/started-utc.txt"
cat /proc/self/cgroup >"$out/cgroup.txt"
cg=$(awk -F: '$1 == "0" {print $3}' /proc/self/cgroup)
for prop in memory.high memory.max memory.swap.max pids.max; do
  cat "/sys/fs/cgroup$cg/$prop" >"$out/$prop"
done
[[ $(cat "$out/memory.max") == 8589934592 && $(cat "$out/memory.swap.max") == 0 ]] || exit 2
export CARGO_TARGET_DIR=$task/sbf-target-verifier
export CARGO_NET_OFFLINE=true
export RUSTFLAGS='-C link-arg=-Wl,--threads=4'
# SBF invokes rust-lld directly, rather than through the native cc driver.
# cargo-build-sbf concatenates RUSTFLAGS with this target-specific form, so
# remove the cc spelling only for that invocation (native jobs keep it).
export CARGO_TARGET_SBPF_SOLANA_SOLANA_RUSTFLAGS='-C link-arg=--threads=4'
export PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin
unset ASPIS_R1_POOL_PROGRAM_ID ASPIS_R1_REGISTRY_PROGRAM_ID
if [[ $mode == devnet ]]; then
  export ASPIS_R1_POOL_PROGRAM_ID=$(jq -er .programs.pool "$task/r1-devnet.template.json")
  export ASPIS_R1_REGISTRY_PROGRAM_ID=$(jq -er .programs.registry "$task/r1-devnet.template.json")
fi
printf 'pool=%s\nregistry=%s\nRUSTFLAGS=%s\n' "${ASPIS_R1_POOL_PROGRAM_ID-default}" "${ASPIS_R1_REGISTRY_PROGRAM_ID-default}" "$RUSTFLAGS" >"$out/environment.txt"
printf 'CARGO_TARGET_SBPF_SOLANA_SOLANA_RUSTFLAGS=%s\n' "$CARGO_TARGET_SBPF_SOLANA_SOLANA_RUSTFLAGS" >>"$out/environment.txt"
echo 'Expected time: incremental optimized SBF compilation, no proof generation.' >"$out/expectation.txt"
cd "$task/src"
command=(/home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin/cargo-build-sbf
  --manifest-path "$task/src/programs/r1-cost-probe/Cargo.toml"
  --sbf-out-dir "$task/artifacts/$mode" --features pool-adapter,private-leaf-salts
  --skip-tools-install --offline -j 4 -- --locked)
printf '%q ' "${command[@]}" >"$out/command.txt"
status=0
/usr/bin/time -v -o "$out/time.txt" env -u RUSTFLAGS "${command[@]}" >"$out/stdout.txt" 2>"$out/stderr.txt" || status=$?
echo "$status" >"$out/exit.txt"
cat "/sys/fs/cgroup$cg/memory.peak" >"$out/memory.peak"
date -u +%FT%TZ >"$out/finished-utc.txt"
if [[ $status == 0 ]]; then
  sha256sum "$task/artifacts/$mode/aspis_r1_cost_probe_program.so" >"$out/artifact.sha256"
  stat -c '%s bytes' "$task/artifacts/$mode/aspis_r1_cost_probe_program.so" >"$out/artifact.size"
fi
exit "$status"
