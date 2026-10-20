#!/bin/sh
# usage: gates.sh <gate>...  One optimized (release) cargo command per gate,
# each in its own capped scope with a receipt (capped-run.sh). Sequential.
set -eu
H=/home/dombarker/project-offloads/codex-cx-stage2b-20261020
S=$H/src; R=$H/harness-r7/capped-run.sh
F=/home/dombarker/project-offloads/codex-r1-format-adopt-20261019/runs/adopt/transfer-1023/task
OLD=/home/dombarker/project-offloads/aspis-r1-worker-b-1h-native-20261019/fixtures
C="--release --offline --locked -j 4"
for g in "$@"; do case $g in
  codec) $R gate-codec-1233 "codec trace: ~1 min" $S -- cargo run $C -p aspis-statement --features r0,pool-v1-kernel --example j1_terminal_codec_trace ;;
  counter) $R gate-counter-adopted "ordered hash trace, adopted verifier: ~1 min" $S -- cargo run $C --manifest-path tools/r1-hash-input-counter/Cargo.toml -- $F/r1-s2-proof.bin $F/r1-s2-public-asf8.bin $H/runs-r7/counter-adopted.json format-adopt ;;
  counter-audit) CARGO_TARGET_DIR=$H/native-target-audit $R gate-counter-audit-eight-way "ordered hash trace, eight-way audit verifier on the decision-1h fixture: ~1 min" $S -- cargo run $C --manifest-path tools/r1-hash-input-counter/Cargo.toml --features audit-eight-way -- $OLD/r1-s2-proof.bin $OLD/r1-s2-public-asf8.bin $H/runs-r7/counter-audit-eight-way.json format-adopt ;;
  program) $R gate-program-lib-inputs-complete "program lib tests incl. 23 checkpoint tests: ~2 min" $S -- cargo test $C -p aspis-r1-cost-probe-program --features pool-adapter,private-leaf-salts --lib -- --test-threads=1 ;;
  crate-default) $R gate-crate-default "crate lib+integration tests, default features: ~2 min" $S -- cargo test $C -p aspis-r1-cost-probe ;;
  crate-detail) $R gate-crate-detail "crate tests with detail-phases,optimized-terminal: ~2 min" $S -- cargo test $C -p aspis-r1-cost-probe --features detail-phases,optimized-terminal --lib ;;
  crate-prover) $R gate-crate-prover-r1p "crate lib tests with prover,r1p-check (retry tests prove ~40 s each): ~15 min" $S -- cargo test $C -p aspis-r1-cost-probe --features prover,r1p-check --lib -- --test-threads=1 ;;
  crate-audit) CARGO_TARGET_DIR=$H/native-target-audit $R gate-crate-audit "crate tests with audit-eight-way: ~2 min" $S -- cargo test $C -p aspis-r1-cost-probe --features audit-eight-way ;;
  guard-prover) CARGO_TARGET_DIR=$H/native-target-audit $R guard-audit-with-prover "expected compile_error" $S -- cargo check --offline --locked -j 4 -p aspis-r1-cost-probe --features audit-eight-way,prover ;;
  teeth) $R gate-teeth-inputs-complete "proof-size teeth on the adopted build: prove ~10 s" $S -- cargo run $C -p aspis-r1-cost-probe --features prover --example proof_size_s2 ;;
  auth) $R gate-authenticated-tx2 "authenticated tx2 gate" $S -- cargo run $C -p aspis-r1-cost-probe --features prover --example authenticated_tx2_gate ;;
  masked) test ! -e $H/runs-r7/masked-gate; $R gate-masked-fixture "masked fixture gate (S2 transfer+withdrawal)" $S -- cargo run $C -p aspis-r1-cost-probe --features prover --example masked_fixture_gate -- $H/runs-r7/masked-gate ;;
  retry) $R gate-r1p-retry "Proof generation plus P_R1 certificate emit/build/check: 8 attempts and retry, optimized, ~8 min; cached compilation" $S -- cargo run $C -p aspis-r1-cost-probe --features r1p-check --example r1p_retry_gate -- 8 $H/runs-r7/r1p-ledger $H/runs-r7/r1p-retry-gate.json ;;
  pool-default) $R gate-pool-default "aspis-pool tests default" $S -- cargo test $C -p aspis-pool ;;
  pool-r1) $R gate-pool-r1-features "aspis-pool tests r1 features" $S -- cargo test $C -p aspis-pool --features r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit ;;
  pool-all) $R gate-pool-all-features "aspis-pool tests all features" $S -- cargo test $C -p aspis-pool --all-features ;;
  pool-v7) $R gate-pool-v7-candidate "aspis-pool tests v7 candidate" $S -- cargo test $C -p aspis-pool --features v7-pair-forest-one-tx-candidate ;;
  wallet) cp $H/harness-r7/wallet-Cargo.lock $S/crates/aspis-pool-wallet-v1/Cargo.lock; CARGO_TARGET_DIR=$H/wallet-target $R gate-wallet "wallet tests eight-lane-plumbing-v2 (B1 refreshed lock)" $S/crates/aspis-pool-wallet-v1 -- cargo test --release --offline --locked -j 4 --features eight-lane-plumbing-v2 --no-fail-fast ;;
  driver-repo) CARGO_TARGET_DIR=$H/driver-target-repo $R gate-repo-pool-gate-build "repo pool_gate build" $S/tools/r1-cost-probe -- cargo build --release --offline --locked -j 4 --bin pool_gate --features private-leaf-salts ;;
  *) echo "unknown gate $g";;
esac; done
