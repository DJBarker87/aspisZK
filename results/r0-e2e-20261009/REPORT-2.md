# R-E2: stopped at the reachable-stack gate

**R-E2 is incomplete. The rebuilt verifier still has reachable SBF stack diagnostics. Work stopped at the user’s explicit stop condition; this ELF was not executed. Completed verifier CU, measured phase CU, headroom to 1.3M/1.4M, and eventual transaction fit remain unmeasured.** A compiler exit of zero does not make this a valid SBF build.

Base: `origin/v8-reference` at `3fb27a8ad`. Branch: `codex/r0-e2e-re2-20261009`. The counters, primitive measurements and pre-refactor estimate were committed first as `1b65149d6`. The subsequent verifier candidate and evidence are retained for review, not presented as a completed on-chain verifier. No co-author trailer is used.

## Stop evidence

The direct source call chain is `process_r0_cu_probe_instruction → r0_verify → verify_semantics_heap`. At least these two reachable functions still fail the 4,096-byte frame requirement:

| Function | Reported stack offset | Estimated frame | Frame excess |
|---|---:|---:|---:|
| `verify_semantics_heap` | 4,224 | 4,416 | 320 |
| `r0_verify` | 4,112 | 4,160 | 64 |

The compiler also reports four calls in `r0_verify` overwriting frame values. [Exact diagnostics](re2/shaped-sbf-stack-diagnostics.json) and [full build log](re2/shaped-sbf.log) are preserved, including diagnostics for the retained dense/prover code. Those other diagnostics have not all been classified for reachability; the two direct reachable failures already require stopping. The terminal evaluator and new `onchain` opening helpers have no named stack diagnostics in this build; that does not close the whole-path stack gate.

The [SBF build](re2/shaped-sbf.json) returned zero after 23.522 seconds, with sampled aggregate RSS 1,181.75 MiB, cgroup peak 934.32 MiB and zero scope swap. The invalid [ELF](re2/shaped-elf/aspis_verifier.so) is 720,168 bytes, SHA-256 `b93394ecb26c9b746aad206068333b4901182accefe15914b0a456b7a2fedb2b`. It is an evidence artifact, not a deployment candidate.

No corrective rebuild, five-run series, higher-CU diagnostic run, or fixture regeneration was started after this stop. No memory cap was raised, and no unchanged measurement was rerun.

## Completed before the stop

1. **Operation counts and SBF primitive calibration.** [CU-ESTIMATE.md](CU-ESTIMATE.md) was written and committed before the deep refactor. Both dense-baseline native fixture verifications accepted. Inclusive counts audit tower arithmetic; exclusive counts avoid pricing nested QM31/M31 work twice. The SBF primitive probe completed 108 distinct work/empty-loop transactions, covering 27 primitives at N=64 and N=128, with simulation/execution agreement. The baseline product estimate is 1,033,623,952 CU for transfer and 1,033,613,497 CU for withdrawal. These estimates describe the old dense path, **not the shaped candidate**, and are neither bounds nor completed verifier measurements. Calibration includes data-dependent arithmetic and call-site limitations documented in the estimate.
2. **Structured quotient transpose.** The carry recurrence implements multiplication by X in the natural basis, using the fixed 512-entry M31 table for the truncated D9 overflow. Y contributes the parity swap and `1 − X²`; the transpose uses two applications of the truncated X transpose. Rows 510/511 use degree, parity and the leading-coefficient recurrence. The optimized [dense comparison gate](re2/structured-gate.log) passed **all 1,024 unit vectors for four `(a,b,c)` choices** (all-one, X-only, Y-only, and a dense E triple), plus eight random E vectors per choice: **4,096 unit comparisons and 32 random comparisons**. Every column of rows 510/511 also matched. Arithmetic runtime was 57.695 seconds. No mismatch occurred. The generator, fixed table and comparison program are retained under `crates/aspis-core`.
3. **Verifier storage candidate.** `OpeningView` validates the whole fixed P1 encoding and all canonical scalars before chord/claim preparation, while borrowing final coefficients and fibre bytes. Semantic claims and handoff/data structures use fallible heap allocation. The interpolant is represented by its three potentially nonzero coefficients. The inactive indicator is a constant bit table; equality weights use QM31 tensor doubling and mixed multiplication into E. The structured map consumes a weight slice and caller-owned scratch, so it does not hard-code the origin or number of claim-weight rows. D14 is not added. The dense basis/prover APIs remain off-chain reference code and are absent from the new `r0_verify` source path.
4. **Native preservation checks.** Both fixtures accepted and round-tripped. The existing **1,894 rejection cases** passed against the shaped verifier, with added direct shaped V1/V2 corruption assertions and comparison of reconstructed polynomials/query sets against the dense preparation path. [Test log](re2/shaped-e2e-tests.log), [resource record](re2/shaped-e2e-tests.json), [cases](re2/shaped-corruption-cases.json). Arithmetic formulas, transcript bytes and check sequence were retained; the semantic evaluator’s 87-value temporary was moved into a separate small helper, and a heap-claim version repeats the same semantic verification sequence. No semantic relation was redesigned or check disabled.
5. **Heap model.** A native allocation wrapper models the non-freeing SBF bump allocator during `r0_verify`, including alignment and allocations that are subsequently freed. Both variants used **121,720 bytes**, plus the 8-byte allocator cursor: 140,416 bytes below 256 KiB. [Usage](re2/shaped-memory-usage.json). This excludes entrypoint/account decoding and diagnostic logging and is **not an observed SBF heap high-water mark**. The diagnostic program now selects a 256 KiB allocator, matching the existing harness’s `request_heap_frame`; end-to-end runtime heap validation remains blocked by the stack gate.

Native checks used [shaped-v1 source hashes](re2/shaped-native-source-manifest.json). The [SBF source hashes](re2/shaped-sbf-source-manifest.json) differ only in the handoff point-comparison representation: an elementwise comparison replaces a temporary mapped E array. That last representation change was compiled by SBF but not rerun natively after the stop. [Structured-gate hashes](re2/structured-source-manifest.json) and [table-generator hashes](re2/weight-table-source-manifest.json) identify their earlier source snapshots; subsequent formatting did not change the structured formulas.

## Fixtures, sizes and comparison with M1

The two proof files and public contexts are unchanged from the base. [Artifact manifest](re2/artifact-manifest.json) pins their hashes and both ELFs. No R-E2 prover generation run was completed, so there is no new byte-for-byte regeneration claim or new prover timing/RSS measurement. The original R-E generation evidence remains historical.

| Measurement | M1 historical diagnostic | R-E2 transfer | R-E2 withdrawal |
|---|---:|---:|---:|
| Proof bytes | 54,604 | 95,712 | 95,712 |
| Sealed ASPU proof-account bytes | different transport | 95,752 | 95,752 |
| ASF8 public-context bytes | different transport | 1,880 | 1,880 |
| Native accepted | PoW bypass | yes | yes |
| Completed SBF verifier CU | 987,814 | unmeasured | unmeasured |
| Headroom to 1.3M | 312,186 | unmeasured | unmeasured |
| Headroom to 1.4M | 412,186 | unmeasured | unmeasured |
| R-E2 verifier CU runs | — | 0: stack stop | 0: stack stop |
| Current transaction-fit conclusion | historical diagnostic scope only | unresolved | unresolved |

M1’s historical phase intervals were 140,757 CU for semantic transcript/sumcheck, 286,713 for terminal evaluation, 149,891 for relation/final-polynomial work, 231,316 for aggregate query arithmetic, 176,047 for Merkle and 3,090 other CU. These are different algorithms and not an R0 budget allocation. See [M1’s report](../v8-state-only-cu-20261009/README.md). All R-E2 completed phase CU fields remain unavailable. R-E’s failed 17.6k-CU invocations are not reused as measurements here. This report supersedes R-E’s overstatement that the stack crash established an eventual one-transaction CU failure.

## Natural split boundaries (unmeasured, not implemented)

These are computational continuation points already exposed by the phase observer, not a reviewed multi-transaction acceptance protocol. Every continuation would need binding to the same immutable proof/public context, protocol identity, and authenticated progress state; no new continuation account or authority design is implemented here.

| Boundary | Computation completed | State needed by the remaining computation |
|---|---|---|
| After semantics | Strict semantic parse, transcript/sumcheck/terminal checks, circle checks and handoff point convention | State before row 25, C1/C2 roots, 25 K challenges, 87 E claims, the two semantic circle points for the replay-equality check, and binding to the sealed proof/public context. The opening parser and all opening checks remain. |
| After k fibres, 0 ≤ k ≤ 22 | Chord/claim preparation, and Merkle then V1 for exactly the first k sorted sampled fibres | Prepared opening data (roots, circle points, endpoints, statement points and claims), gamma/kappa/tau/alpha, reconstructed seven coefficients, the fixed 22-query list, next index k, and the same proof/public binding. Final coefficients and remaining paths can remain in the immutable proof account. |
| Before V2 | All 22 authentication/V1 pairs completed | Circle points/line, three statement points, kappa/tau/alpha, seven reconstructed coefficients, final-coefficient bytes or their bound proof account, and authenticated completion of the preceding phases. Gamma, endpoints and prior paths are no longer computational inputs to V2. |

No CU-fit claim for any split is possible from the current evidence. The baseline estimate is not substituted for measurements of these shaped continuations.

## Resource discipline and remaining work

Every Linux job used its own scope with **MemoryHigh=4 GiB, MemoryMax=6 GiB, MemorySwapMax=0**. Active reservations were checked against a 50 GiB safe total. Release arithmetic and cached builds were used. Source manifests, reservation snapshots, exact commands, wall/RSS/cgroup/swap records and logs are in `re2/`. The initial launcher source audit rejected missing copied source files before any build; those files were transferred and the audit then passed. There was no failed arithmetic gate rerun. Generated task keys remain retained on the build host with mode 0600; no network transaction or deployment occurred.

Remaining gates are the reachable-stack failures, full SBF heap validation, the requested five runs per variant at 1.4M, any explicitly labelled higher-limit diagnostic measurement, measured split budgets, and final fixture regeneration/production-feature checks. This is Rust evidence only; `#print axioms` is not applicable and no formal release obligation is closed.
