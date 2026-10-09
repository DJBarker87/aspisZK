# R-E3: valid SBF verifier and measured phase CU

R-E3 is complete as a verifier measurement task. **The SBF stack gate passes. Both fixtures complete only in the explicitly elevated-CU DIAGNOSTIC runs: transfer 19,335,682 verifier CU; withdrawal 19,325,526. All ten acceptance runs exhaust 1,400,000 CU during Semantic, after Parsed and before any verification phase completes.** The observed SBF heap high-water mark is 131,080 bytes for both fixtures, below 262,144 bytes.

Base: `origin/v8-reference` at `41603fce0ca204804748a3ccad03c65f6eb536c1`. Branch: `codex/r0-e2e-re3-20261009`. Implementation and harness: `d04ecf4b098967e460b23f353f4afbdca1af9c75`. No co-author trailer. The source and evidence are retained; no network deployment or transaction was performed.

## Verifier changes and preservation

`VerifiedSemanticsHeap.before_z1` is now a fallibly allocated box filled by the unchanged row-26 decoder in a separate non-inlined helper. This removes the 928-byte retained array and its copies from the two formerly oversized frames. The semantic formulas, canonicality checks, transcript sequence, and circle checks are unchanged.

`onchain::prepare` owns one boxed `V1Invariants`: gamma powers, the three nonzero interpolant coefficients, the secant line, and four alpha powers. Each V1 borrows it. Claim-prime reuses the same interpolant. The original V1 evaluated its degree-three alpha polynomial by Horner; the new path uses the prepared powers. Native differential builds assert byte equality with the original Horner result for every reached V1. E multiplication is unchanged. There is no fourth opening row or continuation implementation.

The unhoisted on-chain-shaped implementation is frozen verbatim from the base in `onchain_unhoisted.rs` behind the native-only `r0-hoist-reference` feature. The end-to-end differential wrapper compares exact errors, phase order, challenge bytes and query sets for both fixtures and every end-to-end mutation. Fixed-challenge V1/V2 rejection teeth also explicitly compare the unhoisted path. Invariants and the reconstructed polynomial are compared with the dense reference on both fixtures. [Native differential evidence](re3/native-differential-fixed-challenge.log) passes two tests and all **1,894 rejection cases**. The resulting case records equal R-E2’s JSON exactly.

Both fixtures were regenerated once with the unchanged optimized prover. Their proof and public-context bytes equal the base fixtures, and strict native verification and round-trip encoding pass. [Preservation hashes](re3/preservation.json), [transfer regeneration](re3/regenerated/transfer.fixture.json), [withdrawal regeneration](re3/regenerated/withdrawal.fixture.json). Each proof is 95,712 bytes; sealed ASPU account 95,752 bytes; ASF8 public context 1,880 bytes. The signed verifier-only TxV1 proposal serializes to 261 bytes; CU execution here uses legacy transactions. [Production guard](re3/production-tag-guard.log) confirms the production entrypoint still rejects tag 241.

## SBF stack gate: call graph, including indirect calls

`cargo build-sbf --manifest-path programs/aspis-verifier/Cargo.toml --sbf-out-dir results/r0-e2e-20261009/re3/elf-v1 --no-default-features --features r0-cu-probe -- --locked -j 2` exits 0. It reports no diagnostics for either formerly oversized live function. The gate is the complete reachable set, not the compiler exit code alone.

The audit starts at `process_r0_cu_probe_instruction`, follows SBF relative calls, and conservatively allows every `callx` to reach every retained function (including callbacks, formatting, allocation, and error paths). This overapproximation covers **262 linked functions**. All **55 stack/frame-overwrite diagnostic lines**, belonging to **32 functions**, concern symbols absent from the complete unstripped linked ELF and its function bodies. Therefore the reachable diagnostic set is **empty**, even with that conservative indirect-call closure. No classification relies on a function’s name.

[Audit JSON and full edges](re3/stack/stack-audit.json), [symbol table](re3/stack/symbols.txt), [disassembly](re3/stack/disassembly.txt), [build log](re3/sbf-v1.log), [audit script](../../scripts/r0_re3_stack_audit.py). The unstripped audit ELF and stripped measurement ELF have identical `.text` SHA-256: `7ebba1593cfdd662f7122b65aa98b1a3f8a92a8fcfa2e08c3459cb7d71a0f38e`. The measurement ELF SHA-256 is `890107674e4e81b80e7e91b681b22e64dceefd8f94752b34fdc429c6021e2be7`.

Every remaining diagnostic is listed below. **Reason U for every row:** the function body was removed at final link, so it cannot be reached from the root by a direct or indirect call. The live source route uses `verify_semantics_heap`, `semantic_handoff_heap`, `OpeningView`, and `onchain::{prepare,check_v1,check_v2}`. Owned parsing/encoding, by-value semantics, dense opening maps and prover entrypoints are outside that route. Multiple overwrite lines for one function are included in its diagnostic count.

| Unreachable function | Estimated frame (B) | Diagnostic lines | Reason |
|---|---:|---:|---|
| `aspis_core::state_only_prefix::r0::Prefix::point_claims` | 9536 | 1 | U |
| `aspis_core::r0::fold::fold_message` | 8384 | 1 | U |
| `aspis_core::r0::wire::OpeningProof::parse` | 37248 | 1 | U |
| `aspis_core::r0::wire::OpeningProof::encode` | 10240 | 1 | U |
| `aspis_core::r0::wire::Reader::fields` | 8256 | 1 | U |
| `aspis_core::r0::chord::lift_linear` | 98368 | 5 | U |
| `aspis_core::r0::chord::chord_message` | 131328 | 1 | U |
| `aspis_core::r0::chord::polynomial_pair` | 98368 | 5 | U |
| `aspis_core::r0::prover::Commitment::new` | 65856 | 1 | U |
| `aspis_core::r0::prover::honest_claims` | 37568 | 1 | U |
| `aspis_core::r0::prover::EncodingDomain::encode` | 12608 | 1 | U |
| `aspis_core::r0::prover::prove` | 188992 | 1 | U |
| `aspis_core::r0::prover::quotient` | 328128 | 3 | U |
| `aspis_core::r0::prover::v_honest` | 99456 | 1 | U |
| `aspis_core::r0::encoder::eval_message` | 33152 | 1 | U |
| `aspis_core::r0::opening::OpeningData::claim_prime` | 98432 | 1 | U |
| `aspis_core::r0::opening::OpeningData::total_weights` | 196992 | 1 | U |
| `aspis_core::r0::opening::OpeningData::interpolant_batch` | 34112 | 1 | U |
| `aspis_core::r0::opening::OpeningData::weights` | 394560 | 1 | U |
| `aspis_core::r0::opening::OpeningData::q_weights` | 229696 | 9 | U |
| `aspis_core::r0::opening::row_eq_weight` | 32960 | 1 | U |
| `aspis_core::r0::opening::eq_weight` | 65536 | 1 | U |
| `aspis_core::r0::opening::indicator` | 32832 | 1 | U |
| `aspis_core::r0::verifier::verify` | 41408 | 6 | U |
| `aspis_core::r0::verifier::prepare` | 12928 | 1 | U |
| `aspis_core::r0::verifier::check_v1` | 75392 | 1 | U |
| `aspis_core::r0::verifier::check_v2` | 106816 | 1 | U |
| `aspis_statement::state_only_verify::r0::verify_semantics` | 15104 | 1 | U |
| `aspis_statement::r0::semantic_handoff` | 15872 | 1 | U |
| `aspis_statement::r0::Proof::encode` | 22528 | 1 | U |
| `core::array::try_from_fn` | 32768 | 1 | U |
| `alloc::vec::Vec<T,A>::extend_trusted` | 65600 | 1 | U |

## Acceptance: 1,400,000 CU, both fixtures × 5

All five repetitions per fixture have identical errors, marker values, and verifier CU. They are the requested reproducibility series, not extra reruns. No simulation duplicates were executed.

| Fixture / runs | Last completed marker | Semantic complete? | Last marker remaining CU | Transaction CU at abort | Verifier log CU at abort |
|---|---|---|---:|---:|---:|
| transfer, 1–5 | Parsed | no | 1,392,074 | 1,400,000 | 1,399,644 |
| withdrawal, 1–5 | Parsed | no | 1,392,126 | 1,400,000 | 1,399,644 |

Each error is `InstructionError(2, ProgramFailedToComplete)` with runtime log `exceeded CUs meter at BPF instruction`. No stack access error occurs. The transaction meter and program-consumption log are reported separately; the latter is not the full transaction meter. Raw logs are in every [transfer record](re3/acceptance/transfer-run-1.json) and [withdrawal record](re3/acceptance/withdrawal-run-1.json), with runs 2–5 beside them. No completed Semantic or later phase CU is inferred from these aborted runs.

## DIAGNOSTIC: completed runs, same ELF, elevated CU only

One run per fixture uses LiteSVM 0.16.0 / Agave 4.2.1 and `with_compute_budget` at **200,000,000 CU**. The heap remains **256 KiB**, all other compute-budget defaults match LiteSVM’s pinned mainnet feature set, and the native cgroup caps remain 4/6 GiB with swap 0. The serialized compute-budget instruction remains 1.4M; the diagnostic runtime override is explicit in the records. These completed runs are **not acceptance claims**. Both execute the exact acceptance ELF. No additional unchanged measurements were run.

Phase CU is the difference between consecutive `sol_log_compute_units` markers. It includes boundary logging and phase-local parsing/control overhead. Semantic includes the semantic handoff; ChordClaims includes strict opening parsing and preparation; each Merkle includes leaf hashing and path checks. The total program CU additionally includes entrypoint decoding and the tail outside these phase intervals.

| Phase | PLAN prediction transfer | DIAGNOSTIC transfer | Measured / predicted | PLAN prediction withdrawal | DIAGNOSTIC withdrawal | Measured / predicted |
|---|---:|---:|---:|---:|---:|---:|
| Semantic | 1,212,821 | 2,693,892 | 2.221× | 1,209,192 | 2,689,719 | 2.224× |
| ChordClaims | 475,090 | 1,008,549 | 2.123× | 475,090 | 1,007,824 | 2.121× |
| Merkle × 22 | 213,982 | 641,001 | 2.996× | 213,982 | 641,165 | 2.996× |
| V1 × 22 | 7,982,741 | 3,476,468 | 0.435× | 7,975,915 | 3,475,098 | 0.436× |
| V2 | 11,873,991 | 11,507,624 | 0.969× | 11,873,991 | 11,503,624 | 0.969× |
| Verifier total | 21,758,623 | 19,335,682 | 0.889× | 21,748,168 | 19,325,526 | 0.889× |

The predictions are the PLAN’s **unhoisted shaped-path** table, reproduced with its retained lead counts and primitive prices; withdrawal phase values come from the companion withdrawal counts. V1’s lower ratio includes the requested hoisting and is not a prediction of an unchanged algorithm. Against PLAN’s separate approximate **17.5M after hoisting** total, measured transfer is 1.105× (about 10.5% higher). The primitive model did not price full parser/control/allocation/logging overhead or a SHA call base cost, and primitive costs are call-site dependent; these measurements do not assign an exact cause to each residual. V2 is close to the estimate, while Semantic, ChordClaims and Merkle exceed it.

| Fibre index in sorted query order | Merkle transfer | V1 transfer | Merkle withdrawal | V1 withdrawal |
|---:|---:|---:|---:|---:|
| 0 | 30,245 | 157,916 | 30,319 | 157,858 |
| 1 | 29,074 | 158,106 | 29,069 | 157,720 |
| 2 | 29,074 | 158,061 | 29,091 | 158,133 |
| 3 | 29,083 | 158,351 | 29,085 | 157,758 |
| 4 | 29,049 | 157,833 | 29,071 | 157,906 |
| 5 | 29,076 | 158,084 | 29,064 | 158,055 |
| 6 | 29,077 | 158,192 | 29,094 | 158,005 |
| 7 | 29,080 | 157,394 | 29,075 | 158,121 |
| 8 | 29,074 | 158,083 | 29,092 | 158,243 |
| 9 | 29,098 | 158,451 | 29,072 | 157,621 |
| 10 | 29,075 | 157,656 | 29,087 | 157,444 |
| 11 | 29,096 | 158,239 | 29,092 | 158,347 |
| 12 | 29,090 | 157,986 | 29,074 | 157,595 |
| 13 | 29,087 | 158,116 | 29,102 | 158,125 |
| 14 | 29,084 | 157,717 | 29,091 | 158,073 |
| 15 | 29,094 | 158,230 | 29,112 | 158,719 |
| 16 | 29,083 | 157,984 | 29,098 | 157,822 |
| 17 | 29,095 | 157,585 | 29,097 | 157,684 |
| 18 | 29,100 | 158,318 | 29,100 | 158,115 |
| 19 | 29,089 | 157,877 | 29,096 | 157,952 |
| 20 | 29,097 | 157,975 | 29,094 | 157,609 |
| 21 | 29,081 | 158,314 | 29,090 | 158,193 |

| Total / resource | Transfer | Withdrawal |
|---|---:|---:|
| Transaction CU including budget instructions/runtime overhead | 19,336,038 | 19,325,882 |
| Program CU outside the five phase groups | 8,148 | 8,096 |
| SBF heap high-water bytes, including 8-byte cursor | 131,080 | 131,080 |
| Heap headroom below 262,144 bytes | 131,064 | 131,064 |
| CU headroom to 1.4M | −17,935,682 | −17,925,526 |
| CU headroom to 1.3M | −18,035,682 | −18,025,526 |
| Ratio to 1.4M | 13.811× | 13.804× |

The heap is observed inside SBF after V2, using the non-freeing bump cursor and non-allocating `sol_log_64`. It includes account decoding, entrypoint and phase-log allocations, plus the cursor reservation. Because the SBF allocator never frees, every earlier SBF allocation remains included. Successful completion proves this invocation stayed inside the requested heap. The raw heap line is `0x20008`.

The two fixtures differ by 10,156 verifier CU; the full phase breakdown preserves those data-dependent differences. [Transfer DIAGNOSTIC](re3/diagnostic/transfer-diagnostic-1.json), [withdrawal DIAGNOSTIC](re3/diagnostic/withdrawal-diagnostic-1.json), [machine-readable summary](re3/summary-3.json). A budget ratio is not an implemented or measured transaction count for a continuation protocol.

## Resource and evidence record

Every Linux build, test, proof generation, audit and measurement uses its own scope with `MemoryHigh=4294967296`, `MemoryMax=6442450944`, `MemorySwapMax=0`. Reservation snapshots enforce a 50 GiB safe host total; at most two task scopes overlap (12 GiB combined reservation). All records report zero scope swap. Optimized release binaries execute arithmetic; expected execution work was recorded before CU runs and fixture regeneration. The same pinned workspace and target cache were reused. No memory cap was raised.

| Job | Exit | Wall seconds | Sampled aggregate RSS MiB | cgroup peak MiB | Swap B |
|---|---:|---:|---:|---:|---:|
| [native-differential](re3/native-differential.json) | 101 | 0.501 | 12.65 | 10.86 | 0 |
| [native-differential-complete-workspace](re3/native-differential-complete-workspace.json) | 0 | 36.539 | 1049.92 | 830.49 | 0 |
| [sbf-v1](re3/sbf-v1.json) | 0 | 71.063 | 1187.39 | 1133.24 | 0 |
| [stack-audit](re3/stack-audit.json) | 0 | 0.501 | 12.68 | 32.13 | 0 |
| [driver-build](re3/driver-build.json) | 101 | 128.613 | 1064.88 | 1403.42 | 0 |
| [driver-build-public-api](re3/driver-build-public-api.json) | 0 | 1.501 | 372.76 | 179.64 | 0 |
| [native-differential-fixed-challenge](re3/native-differential-fixed-challenge.json) | 0 | 2.002 | 206.27 | 123.56 | 0 |
| [acceptance-transfer](re3/acceptance-transfer.json) | 0 | 0.501 | 12.67 | 22.82 | 0 |
| [acceptance-withdrawal](re3/acceptance-withdrawal.json) | 0 | 0.501 | 12.67 | 22.97 | 0 |
| [diagnostic-transfer](re3/diagnostic-transfer.json) | 0 | 0.501 | 12.71 | 21.87 | 0 |
| [diagnostic-withdrawal](re3/diagnostic-withdrawal.json) | 0 | 0.501 | 12.69 | 21.77 | 0 |
| [regenerate-transfer](re3/regenerate-transfer.json) | 0 | 5.004 | 196.90 | 197.91 | 0 |
| [regenerate-withdrawal](re3/regenerate-withdrawal.json) | 0 | 5.004 | 196.89 | 197.48 | 0 |
| [production-tag-guard](re3/production-tag-guard.json) | 0 | 37.034 | 998.77 | 791.85 | 0 |

Two setup failures are retained: the first native command stopped before compilation because the copied workspace lacked a member manifest; the workspace inputs were completed before retrying. The first harness build used a LiteSVM getter hidden behind an internal-test feature; it was replaced with the public pinned `mainnet_feature_set` API before retrying compilation. Neither failure executed a CU measurement. The final native suite was rerun after adding explicit unhoisted comparisons to the fixed-challenge teeth. No unchanged CU measurement or SBF build was rerun.

[Environment/toolchains](re3/environment-re3.json), [final source manifest](re3/source-manifest.json), [SBF source manifest](re3/sbf-source-manifest.json), [host-test snapshot](re3/host-v2-source-manifest.json), [artifact manifest](re3/artifact-manifest.json). The SBF and first native records identify the exact base plus candidate snapshot through their manifests; changes after the SBF build are confined to native tests, the host harness and audit tooling. All verifier/SBF source hashes match the committed implementation. The sampled RSS interval is 0.5 s, so very short jobs also have the cgroup peak and child high-water values in their JSON.

Generated ELF and LiteSVM payer keys remain on the build host with mode 0600; no keys were deleted and no network refunds were needed. Private key files are excluded from committed evidence. `#print axioms`: not applicable; this is Rust/SBF evidence, with no Lean edits or formal release claim. The task’s stop conditions were not triggered.
