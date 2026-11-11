# PIN2 artefact gate (S1)

base 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387
pin  c7593d23fdc56fcee9a9df1628d5f63b52ac7a95
head d7142292c480303e90c9c96e7f4c60dde9a87961

## Counts

- NOT_NAMED paths: 0
- programs/aspis-pool: pin tree bf9ea55d7ce827b6ba15b06386f94c06fdc9ef0f vs b936275 tree bf9ea55d7ce827b6ba15b06386f94c06fdc9ef0f: equal=True; files compared 20, differing 0
- cumulative changed paths 4bb3b3f..head (whole tree): 93; changed within build scope: 44; build-scope files hashed: 3871
- 43919c0a9f2: 1 paths, classes {'W1': 1}
- 271869c946d: 4 paths, classes {'W1': 4}
- c7593d23fdc: 54 paths, classes {'STREAM_B_SHIPPED': 17, 'STREAM_B_SHIPPED_WORKSPACE_MANIFEST_FLAG': 1, 'DOCS_NOT_SHIPPED': 6, 'STREAM_B_TEST': 15, 'POOL_LINE': 15}
- d7142292c48: 34 paths, classes {'tools': 34}
- tools commit paths outside evidence/scripts/tools: 0; pin..head paths outside evidence/scripts/tools: 0
- build-scope changes not explained by a per-commit class: 0

## Flag
Root Cargo.toml changes by one line (workspace member programs/aspis-upload) and Cargo.lock adds package aspis-upload (deps solana-program, solana-sdk-ids only). Classified STREAM_B_SHIPPED_WORKSPACE_MANIFEST_FLAG because Cargo.toml is not literally in the named shipped set; lead to confirm.

## Changed build-scope paths (4bb3b3f..head)

- Cargo.lock
- Cargo.toml
- crates/aspis-prover/src/state_only_entropy.rs
- crates/aspis-prover/src/state_only_hiding.rs
- crates/aspis-r1-cost-probe/src/host_commitment.rs
- crates/aspis-r1-cost-probe/src/host_semantic.rs
- crates/aspis-r1-cost-probe/src/host_sumcheck.rs
- crates/aspis-r1-cost-probe/src/prover.rs
- crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs
- programs/aspis-pool/src/anchor.rs
- programs/aspis-pool/src/cancel_prepared_settlement_instruction.rs
- programs/aspis-pool/src/deposit.rs
- programs/aspis-pool/src/deposit_transport.rs
- programs/aspis-pool/src/instruction.rs
- programs/aspis-pool/src/lib.rs
- programs/aspis-pool/src/prepared_settlement.rs
- programs/aspis-pool/src/prepared_settlement_format.rs
- programs/aspis-pool/src/prepared_settlement_instruction.rs
- programs/aspis-pool/src/processor.rs
- programs/aspis-pool/src/settle_prepared_instruction.rs
- programs/aspis-pool/src/state.rs
- programs/aspis-pool/src/transition.rs
- programs/aspis-pool/src/vault.rs
- programs/aspis-pool/tests/payment_relation_abi.rs
- programs/aspis-upload/Cargo.toml
- programs/aspis-upload/src/lib.rs
- programs/aspis-upload/src/tests.rs
- programs/r1-cost-probe/src/close_checkpoint_tests.rs
- programs/r1-cost-probe/src/pool_route.rs
- programs/r1-cost-probe/src/r1_checkpoint_tests.rs
- programs/r1-cost-probe/src/r1_pool_adapter.rs
- tools/pin2-upload-litesvm/Cargo.lock
- tools/pin2-upload-litesvm/Cargo.toml
- tools/pin2-upload-litesvm/src/lib.rs
- tools/pin2-upload-litesvm/stub-verifier/Cargo.lock
- tools/pin2-upload-litesvm/stub-verifier/Cargo.toml
- tools/pin2-upload-litesvm/stub-verifier/src/lib.rs
- tools/pin2-upload-litesvm/tests/upload_close.rs
- tools/r1-cost-probe/Cargo.lock
- tools/r1-cost-probe/Cargo.toml
- tools/r1-cost-probe/src/bin/devnet_spend/Client64_accounts.rs
- tools/r1-cost-probe/src/bin/devnet_spend/Pin2_upload.rs
- tools/r1-cost-probe/src/bin/devnet_spend/plan.rs
- tools/r1-cost-probe/src/bin/pv_client_gate.rs
