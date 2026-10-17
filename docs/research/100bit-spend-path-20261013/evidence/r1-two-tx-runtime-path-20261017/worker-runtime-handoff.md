# ASQ8 current Pool compute optimization probe, 2026-10-17

This packet records measured two-transaction ASQ8 transfer and withdrawal success with full OS-random R1 proofs/public. The SBF Pool artifact enables four existing default-off audit paths that skip repeated checks justified by Pool/verifier invariants. The result is classified `UNPROVED R1 S2 POOL-PATH ACCEPTANCE MEASUREMENT`; it is a candidate runtime/CU measurement, not release proof or production authorization.

## Artifacts and source

- Clean, uninstrumented Pool ELF: `../../artifacts/pool-asq8-auditfast-clean/aspis_pool.so`, SHA-256 `45983cab52a04f60cef431afcea0ccb90b1c48456b3a08af83d29522ac3561f5`.
- Pool source is unchanged from the maintained worktree: `pair_forest.rs` SHA `2e0852f4c5dc7ba0b25ac1567b8c3e7c3a52c8038685dad34ec2f29e05eec957`; `pair_forest_dispatch.rs` SHA `95f1d6188c6102ab5724cd9791e96d77c519cb3e88dba09a52532f7882f43ad8`.
- Pool build features: `r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit,pair-forest-direct-result-audit,pair-forest-full-asf8-audit`.
- Verifier ELF: `../../artifacts/candidate-verified/aspis_r1_cost_probe_program.so`, SHA-256 `2ba4725ffaf04ceb761346942950d0d681379b2efb084111893078953518d12c`.
- Registry ELF: `../../artifacts/aux-current/registry/aspis_registry.so`, SHA-256 `7ad46f0d4b102a7c9699149d23bf6e065b6151feeaca95977d0a3146167d01ab`.
- Host gate binary: `../../evidence/gate-bin/pool_gate-candidate-asq8-stage1log`, SHA-256 `4c06599c17c535523beb87e5187e8ae5e5c7060bbae3b9e25563b22c270faf9c`; source SHA `606a80aed4002335e54deb5a997697bca1c6ccd33dad22c64fdea76aac2507d0`.

Clean build command (locked, offline, optimized Solana SBF 3.1.13 / platform-tools 1.52, one job):

```sh
cargo-build-sbf --manifest-path candidate/programs/aspis-pool/Cargo.toml \
  --sbf-out-dir artifacts/pool-asq8-auditfast-clean \
  --features r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit,pair-forest-direct-result-audit,pair-forest-full-asf8-audit \
  --skip-tools-install --offline -j 1 -- --locked
```

It ran in systemd scope `aspis-pool-asq8-auditfast-cleanbuild-20261017` with MemoryHigh 6G, MemoryMax 8G, MemorySwapMax 0; exit 0, 3.18s, peak RSS 297,304 KiB, swap 0. Build log is `logs/pool-asq8-auditfast-clean-build.log`.

## Two measured transactions

Both runs use LiteSVM 0.16, TxV1, 1,400,000 CU cap, the real R1 stage1 instruction [3,10], then compact ASQ8 Pool terminal [3,11] with selected verifier CPI. Proof/public are freshly generated with OS randomness and preloaded as LiteSVM genesis accounts, so there are zero upload/lifecycle transactions; this is not an upload-from-empty-state claim. The gate asserts simulation equals execution, exact lane/history/nullifier settlement, immutable checkpoint/registry/proof, and for withdrawal the exact token delta.

| Flow | Stage 1 CU / bytes | ASQ8 + settlement CU / bytes | Outcome | Main settlement evidence |
| --- | ---: | ---: | --- | --- |
| Transfer | 1,342,839 / 295 | 1,323,012 / 878 | accepted | exact candidate lane, same-page history, and nullifier marker written; verifier checkpoint unchanged |
| Withdrawal | 1,341,600 / 295 | 1,336,800 / 1,043 | accepted | exact candidate lane/history/marker; vault 10,000->9,750 and destination 17->267 |

Each gate run was in its own systemd scope with MemoryHigh 6G, MemoryMax 8G, MemorySwapMax 0; exit 0, 4.46s, peak RSS about 231 MiB, swap 0. Full gate logs are `logs/pool-asq8-auditfast-transfer3.log` and `logs/pool-asq8-auditfast-withdrawal2.log`. Full JSON, ASR2/ASE2, OS-random proof/public, nonce burn, and retained payer/authority keypairs are in `transfer/` and `withdrawal/`; keys have not been deleted.

## CU diagnosis

Instrumented, source-only probes were copied to `source/` and do not enter the clean ELF. With the default strict decoder, the Pool has about 481,905 CU consumed by the time master/checkpoint/lane decoding and account binding finish; ASQ8 CPI then enters with only about 840,805 CU remaining, and the verifier exhausts around query 21. Under the lane source-invariant decoder, the same boundary is about 1,384,559 CU remaining (about 15k CU consumed from entry), saving roughly 468k CU before CPI. Marker planning costs about 54k CU, System create/allocate marker CPI about 6.5k, Registry selection about 10.5k, other dispatcher/account checks about 6.6k. The verifier then completes. Source probe files are `source/pair_forest.instrumented.rs` and `source/pair_forest_dispatch.instrumented.rs`; their hashes are `77e5429619e53484d74e175e651a4c13e53ba6e8794c4d860279abe1327411ee` and `428f3fd661e3ad740fde1e386a7091b6b15abbe3c4a656656ea34b7e0447e1b8`. Strict and source-invariant-only failed profile logs are preserved under `logs/`.

## What the audit features change

- `pair-forest-source-invariant-audit` routes lane decoding through manual canonical header/digest/inactive-frontier checks instead of the general decoder's full active root/frontier relation reconstruction. This relies on the Pool inductive write invariant: initialization writes genesis state; deposits and terminal settlement are the only lane writers and must preserve the relation. The separate formal closure for this persisted-state invariant remains required.
- `pair-forest-source-result-invariant-audit` uses the canonical output encoder that keeps field, capacity, and inactive-frontier checks while relying on the verifier/deposit append invariant instead of recomputing the root/frontier relation again.
- `pair-forest-direct-result-audit` avoids reconstructing a second terminal statement after selected-verifier CPI, retaining direct result/account/nullifier/afterstate-index checks. Its use requires the selected registered verifier's exact source/runtime relation and returned-result binding to remain closed.

These are existing candidate-only/default-off feature paths. Tests establish compute feasibility and runtime state deltas; they do not discharge soundness obligations or authorize production feature enablement. The generated fixtures retain the unproved classification for that reason.

## Passing profile without the direct-result shortcut

A fresh ablation removed both unrelated `pair-forest-full-asf8-audit` and `pair-forest-direct-result-audit`. The passing feature set is exactly `r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit`. It retains the generic authenticated verifier-result validation and the canonical ASR8/ASVS binding path.

- Pool ELF: `minimal-no-direct/artifacts/aspis_pool.so`, SHA-256 `b33302fd0f7deaa135dce11be58b0035e78e2696f0e0c608060418ccfa2975e5`.
- Optimized locked/offline SBF build: exit 0, about 3.2s, peak RSS about 295 MiB, swap 0, own MemoryHigh=6G/MemoryMax=8G/MemorySwapMax=0 scope. Full build log: `minimal-no-direct/pool-asq8-nodirect-build.log`.
- Fresh OS-random transfer: stage1 1,342,815 CU / 295 bytes; ASQ8 terminal plus Pool settlement 1,329,117 CU / 320-byte instruction, accepted.
- Fresh OS-random withdrawal: stage1 1,341,341 CU / 295 bytes; ASQ8 terminal plus Pool settlement 1,342,661 CU / 320-byte instruction, accepted. Vault was 10,000→9,750 and destination 17→267. This is the tight case, with 57,339 CU below the 1.4M cap.
- Both transactions used the selected R1 verifier and Pool path, with proof/public preloaded as genesis accounts; proof upload is outside this measurement. Gate results assert simulation equals execution, exact settled lane/history/nullifier state, immutable checkpoint/registry/proof, and the withdrawal token delta. Full evidence JSON, ASR2/ASE2, proof/public bytes, keypairs, and logs are under `minimal-no-direct/`.

The previous `minimal/` profile with `pair-forest-direct-result-audit` also passed; it remains as historical evidence but is not the minimum feature set. A separate ablation without `pair-forest-source-result-invariant-audit` exhausted after verifier completion, so the source-result encoder feature is required for this measured profile.

The passing profile relies on the already-described Pool source and source-result invariants. It is a runtime/CU measurement, classified `UNPROVED R1 S2 POOL-PATH ACCEPTANCE MEASUREMENT`; it does not close their formal soundness obligations or authorize production enablement.
