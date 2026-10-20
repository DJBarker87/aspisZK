#!/bin/sh
set -eu
H=/home/dombarker/project-offloads/codex-cx-stage2b-20261020
export RUSTFLAGS="-C link-arg=-Wl,--threads=4"
export CARGO_TARGET_SBPF_SOLANA_SOLANA_LINKER=$H/harness-r7/sbf-linker/rust-lld
export CARGO_TARGET_DIR=$H/sbf-target-profile
for kind in baseline; do
 if [ "$kind" = candidate ]; then export ASPIS_SOURCE_ROOT=$H/src ASPIS_SOURCE_REVISION=b2f138abf1af6014470c7fd8c8eb2b03a945dee6; else export ASPIS_SOURCE_ROOT=$H/src-profile-base ASPIS_SOURCE_REVISION=7d4c136f0; fi
 touch $ASPIS_SOURCE_ROOT/crates/aspis-r1-cost-probe/src/candidate.rs $ASPIS_SOURCE_ROOT/crates/aspis-r1-cost-probe/src/verifier.rs $ASPIS_SOURCE_ROOT/crates/aspis-r1-cost-probe/src/multiproof.rs $ASPIS_SOURCE_ROOT/programs/r1-cost-probe/src/lib.rs
 mkdir -p $H/artifacts/profile-$kind-refreshed $H/runs-profile/$kind-refreshed
 $H/harness-profile/capped-run.sh build-$kind-refreshed "Diagnostic cu-profiling SBF compile/link, cached dependencies" $ASPIS_SOURCE_ROOT -- /home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin/cargo-build-sbf --manifest-path $ASPIS_SOURCE_ROOT/programs/r1-cost-probe/Cargo.toml --sbf-out-dir $H/artifacts/profile-$kind-refreshed --features pool-adapter,private-leaf-salts,cu-profiling --skip-tools-install --offline -j 4 -- --locked
 $H/harness-profile/capped-run.sh cu-$kind-refreshed "Diagnostic profiling replay; not release CU evidence" $H -- /home/dombarker/project-offloads/codex-r1-format-adopt-20261019/artifacts/pool_gate_adopt /home/dombarker/project-offloads/codex-r1-cu-bound2-20261019/artifacts/pool/aspis_pool.so $H/artifacts/profile-$kind-refreshed/aspis_r1_cost_probe_program.so /home/dombarker/project-offloads/active-mask-basis-sbf-20261017/artifacts/aux-current/registry/aspis_registry.so $H/runs-profile/$kind-refreshed/evidence.json $H/runs-profile/$kind-refreshed/task transfer success --pairs 13 --reuse /home/dombarker/project-offloads/codex-r1-format-adopt-20261019/runs/adopt/transfer-13/task/r1-s2-proof.bin /home/dombarker/project-offloads/codex-r1-format-adopt-20261019/runs/adopt/transfer-13/task/r1-s2-public-asf8.bin --split 10 --tx-version v1
done
