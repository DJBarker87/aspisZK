# PV_DIAG9 — D463: complete-Result panic corollaries and diagnostic boundaries

**Target not yet established.** Worktree exactly `/Users/dominic/ZK/.worktrees/pv-diag`, sparse checkout, branch `codex/pv-diag9-20261029`, base `679b1e9ee3`. No endpoint premise or complete DIAG acquisition input is removed. This report distinguishes compiler-family success from the full native prover and checker.

## Complete-Result corollaries

`PV_DIAG9_Result` proves that an outer Aeneas `.ok` excludes `.fail .panic`, divergence and every outer failure, including when the returned Rust Result is an error. Successful monadic bind forces both its prefix and its reached continuation to terminate normally. An allowed-outer-error classification also excludes panic when its allowed predicate excludes `.panic`. These preserve the actual Result; no success-only projection is substituted. `post_does_not_exclude_panic` checks that a success-conditional postcondition alone is insufficient.

`PV_DIAG9.honest_compiler_no_panic` (file `PV_DIAG9_Honest.lean`) applies `PV_RunJoin_HonestIdentification26.success` to **every HonestInput compiler invocation**, with no same-public restriction or additional success premise. `canonical_transfer_no_panic` and `canonical_withdrawal_no_panic` obtain this family from `CanonicalHonest31` on the original successful canonical preparations. The entire compiler invocation is covered at once; no enumeration of its panic payloads or guards is needed. This is the compiler/builder model named by `PV_Src_NativeInput.run`, not a theorem about the complete `prover.prove_masked_attempt`.

`PV_DIAG9_Encoders` derives full-invocation panic/divergence exclusion from `EncodedComplete41.encode` and `SemanticComplete40.encode`. `actual_caller_encoder_no_panic` uses **step-1's actual `CallerSuccess43.success` Domain**, then the complete semantic encoder theorem. Its explicit output-capacity obligation remains. `CallerDomain43.post` itself permits outer failure/divergence and is not credited as a termination theorem.

`PV_DIAG9_Retry.retry_no_panic` allows done, Rejected/retry, other returned errors and exhaustion; it requires every supplied attempt to return an outer `.ok`. `PV_DIAG9_Scope.extracted_retry_no_panic` transports that criterion through the **existing exact `ProverRwRetryModel.retry` law** to actual extracted `prover.retry_attempt`. The per-attempt complete-Result producer is still an explicit hypothesis, not derived from HonestInput or erased into trust. This is a whole retry-control corollary, **not unconditional honest whole-prover panic exclusion**.

The Rust-panic → `Result.fail .panic` interpretation is **reclassification within existing Charon/Aeneas tool trust (owner fifth amendment)**, not a newly proved Rust semantics theorem and not a new T item. Existing extraction/fidelity, opaque callback and compiler/runtime boundaries retain their exact scopes; V370 and D381/D386 remain. Failure propagation excludes modelled, propagated panic. A caught/opaque native panic cannot be excluded merely from a normal wrapper return.

## Exact uncovered prover/checker cones and op227 authority

The read-only runjoin handoff retains step (2): the common-sample/toRP completion; actual backend hinput producer through initialization, build_with_material and commitment mutations; FinishContext; both opening constructors, 22 query appends, six node multiproofs/indices; and the ordered publish_compact equation. There is no credited complete honest Result theorem here for the **whole prepare_opening → finish/openings → publish_compact → prove_from_semantics → prove_masked_attempt** chain with its actual callbacks. The generic retry corollary cannot manufacture it. These are function/cone obligations, not another panic-site campaign.

The native public-check wrapper is `docs/research/v8-r0-zk-20261009/z4/z9e.rs:196–220`: `public_data(ch)`, `emit(&p)`, `Lanes::new`, `convert`, `extracted_builders`, `ck::check`, including their workers/callbacks. Its `catch_unwind` maps a caught panic to a false verdict. No complete honest Result producer covering that native cone is supplied by the inspected runjoin theorems. `PV_L2_F6Checker.erases` associates a recorded model with `R1CertCheck.check`; it is not whole-cone termination. Thus **checker-wide honest panic exclusion remains OPEN**. Hook suppression is not exclusion. The failed draft at 66296 illustrating catch control has no formal credit; the source control fact is separately checked in `source-bindings.json`.

`read-only-authority.json` pins every inspected theorem/report to immutable branch revisions and records candidate identity. **Candidate 679b1e9ee3 has the older b3p6 D377 cohort and lacks `PV_B3P_InstalledOk8227` and `TerminalOk8227`.** Resume7's scoped op227 formatting exclusion is read on b3p6's branch and retained as inherited evidence. Its report explicitly does not prove whole reference/installed success. Later branch `installed_nonvacuity8` supplies an existential public/value witness for each claims/point/challenges tuple, not success for every honest original public input. `installed_success8` uses its named constructed public family. Neither is silently installed into this candidate or used to discharge the full prover/checker claim.

## Dynamic operands, logger and captured frames

`source-bindings.json` rechecks **551 pinned build inputs**, enumerates **41 exact selected client diagnostic/format/map_err sites**, and retains the inherited **463 logger candidates** by hash. It does not promote a lexical inventory to honest reachability.

- `plan.rs:21` formats arbitrary Debug `e`. At `:122`, the prover's eleven error variants are unit variants under the deployed prover feature. Their selected variant spelling remains inherited public-content evidence; the joint occurrence/variant law remains L1 work. Other map_err callers are individually retained. `PoolV1PairTraceErrorV1::BlockMismatch {block,local_row,lane}` and `AuxiliaryMismatch {row,column}` carry dynamic coordinates: they are not environment outcomes and are not relabelled public. The successful canonical compiler call cannot return its error branch; arbitrary compiler-error formatting elsewhere has no blanket public law.
- The fixed successful audit value and fourteen active literal messages retain diag8's selected-content credit. Whole JSON/recovery serialization, byte lengths, allocation, timing, delivery and abnormal continuations remain OPEN. Recovery contents are not relabelled public.
- `PV_DIAG9_Operands` keeps site, operands, live frames, level, configuration and mutable logger state explicit. Equal public invocation/state transports complete formatter/logger replies and order, including failures. Its operand-length/capacity transport is a criterion, not a native implementation of `fmt::estimated_capacity`. No actual logger operand is proved public merely because its level/configuration is environmental. The unchanged image/IR evidence has no named directly reached logger dispatch; inlined macros/indirect callbacks remain unclassified and OPEN, with the inherited exact inventory retained.
- **Narrower frame obligation:** `normal_return_restores`, `selected_capture_public_after_return` and `returned_error_callsite_frames` show that arbitrary earlier normal callee/retry paths do not remain on the live stack once the callee has returned. The checked normal-return/map_err order at `plan.rs:122 → :21` therefore removes the need to prove equality of the prover's entire earlier internal control path merely to identify this selected caller stack. This is a model stack theorem plus local source control association. It does **not** prove native PCs/unwinder correspondence or fixed error-site occurrence. All earlier captures/hook/log effects are retained (`earlier_captures_retained`, `complete_capture_transport`); an explicit model counterexample shows normal return does not erase earlier private captures. Constructor/formatting frames, existing backtrace providers, worker/unwind paths, resolver/module/build/cache state, and other capture sites retain their exact native obligations.

No checked same-public honest-witness native diagnostic leak was constructed. Dynamic operand provenance without an honest reachable failing witness is an OPEN obligation, not a finding.

## Option B / V400

D215/V400 stays the **single shared P row**, with the failure signal public to both experiments and the bound and complete observer unchanged. The required event law is conditional witness independence **jointly with original L1 coins/history and every retained observer prefix**. Matching complete histories is a sufficient stronger coupling, not a new definition of V400.

`PV_DIAG9_World.byte_blind_public_replay` proves an adaptive finite-prefix criterion: request metadata/stopping policy is public given the prior history, and the world's reply is payload-blind on that history. Requests retain operation, target/path/fd, offset, requested size, alignment, address class and retry state; replies retain error, code and partial transfer count. Policies may adapt or stop after any reply. Prefixes and variable actual counts are preserved. Small checked model obstructions show equal sizes alone are insufficient, payload-sensitive worlds may differ, and equal Boolean failure events do not imply equal error/history content. These are specification tests, not deployed counterexamples.

A deployed V400 instance must establish those public request laws on the actual client, and prove the world's necessary blindness to bytes, addresses, allocator-written state, filesystem state and scheduling, or derive their public joint laws. The proof-account nonce source can be public under the original entered-index association; fixed entropy request sizes and nonce-write sizes 16/32/32 remain useful inherited facts, not whole-history independence. Actual recovery/proof/statement I/O, reservation state, retries/Interrupted, allocation and concurrency still require the deployed association. Ownership/drop results constrain memory lifetime and cleanup; they do not alone prove failure independence. V336–V339 and E2 remain.

## Exact pv-rj4idb handoff and sink disposition

`PV_DIAG9.DIAG9_inputs_given_native_binding` imports and consumes the **actual existing** `PV_RJ4IDB.OpenInputs.DIAG_FILE_TRACE`, `DIAG_JSON_STDOUT_TRACE`, `DIAG_ERROR_STDERR_TRACE`. It is conditional on those acquisition laws and a public joint native-event law. `decoder_given_complete_native_binding` separately retains the terminal; three channels alone do not supply it. Arbitrary prefix index sets and the existing native decoder/factorization are reused, not duplicated. No acquisition instance is claimed.

| Input / sink | Updated disposition |
|---|---|
| Honest canonical compiler model panics | **NOT REACHED**, whole-invocation corollaries on both original canonical families. |
| Actual semantic compact encoder / encoded_slice | **NOT REACHED** for modelled panic on the named Domain/capacity conditions; no full publisher association inferred. |
| Whole prover / public checker / opaque native callbacks | **OPEN**, exact cones above; conditional extracted retry corollary does not discharge its attempt-law hypothesis. |
| `DIAG_FILE_TRACE` | **OPEN**: inherited local I/O facts plus new adaptive V400 criterion; actual requests/delivery/errors/cleanup acquisition missing. |
| `DIAG_JSON_STDOUT_TRACE` | **OPEN**: inherited audit-content/length facts; whole bytes, order, allocation/time, delivery and abnormal prefixes missing. |
| `DIAG_ERROR_STDERR_TRACE` | **OPEN**: stronger whole-compiler/encoder exclusions and normal-return caller-stack law; native invocation/variant/hook/frames/OOM/crash and complete trace acquisition missing. |
| Unit error spellings / selected literals / audit fields | **Public-only selected content**, inherited; joint site/variant/prefix/delivery law remains. |
| op227 formatting | Inherited **NOT REACHED** in the scoped resume7 cone; authority/installed-success limitations above. |
| Selected returned-error capture after normal prover return | **Public caller-stack criterion proved**, with earlier effects retained; native PC/constructor/site association OPEN. |
| Logger operands/state / other captures / formatter internals | **OPEN**; exact inherited inventories retained; configuration alone insufficient. |
| fd1/fd2 I/O, last_error/strerror/lossy, file errors | Inherited **conditional public environment components** under shared V400 and public requests/operands; whole trace still OPEN. |
| Final Rejected/retry report arms and local extra-emission exclusions | Inherited scoped **NOT REACHED** facts unchanged; earlier effects retained. |
| Panic/OOM/unwind/abort, foreign/fatal/crash/register/raw-memory reporters; final visible state | **OPEN** outside the explicitly covered complete-Result cones. No channel is discarded. |

Endpoint premises removed/added/weakened/changed: **0/0/0/0**. Before and after: full native observer acquisition, original joint L1 law, V400 deployed independence and actual prover/checker producers remain. V038, V178/V181, V336–V339, V347–V351 and V370 remain. T is exactly entropy_law, entropy_kernel, observation. No simulator/observer/soundness/crate/program/release-pin change, key/account/nonce operation, merge or push.

## Verification, rejected work and stop

**100/100 Lean attempts**, IDs **66200–66299**, **91 accepted / 9 rejected**; audits exclusively 66297–66299. **4/30 capped native scopes**, **0 Kani**. All compiler/scope launches required admission exit 0 and allowed:true in the same wrapper. No reservation refusal, void launch, cap increase, resource kill or unchanged failed-source resubmission occurred. Every scope used MemoryHigh 6G, MemoryMax 8G, MemorySwapMax 0, TasksMax64; Lean -M7000.

| ID | Exact target | Exit | GNU wall | Peak RSS KiB | Swap | Launch revision |
|---|---|---:|---:|---:|---:|---|
| 66297 | PV_DIAG9_Audit | 0 | 0:03.08 | 4974092 | 0 | `e803cc2fdda63892eb27d592d71aaa15fe95646c` |
| 66298 | PV_DIAG9_CohortAudit | 0 | 0:01.62 | 2615948 | 0 | `e803cc2fdda63892eb27d592d71aaa15fe95646c` |
| 66299 | PV_DIAG9_FinalManifest | 0 | 0:01.86 | 4996420 | 0 | `e803cc2fdda63892eb27d592d71aaa15fe95646c` |

Lean scopes total wrapper wall **188.40s**, peak RSS **4,996,420 KiB**, swap **0**. All 88 new top-level theorem names are covered by the reserved audits; every printed accepted axiom set is a subset of {propext, Classical.choice, Quot.sound}. `summary.json` and individual receipts retain exact targets/commands, source snapshots and hashes, dependency-object fingerprints, launch revision, exit, wall/RSS/swap and full axioms. Failed internal sorryAx diagnostics are retained and never credited.

Proof sources freeze at **e803cc2fdd**; `proof-source-commit-binding.json` checks all twelve final sources against that commit, and the final summary binds them to accepted snapshots. Earlier receipt launch labels identify the clean base from which the dirty work began; they do not claim the new proof sources existed at that base. The snapshots and freeze binding supply the exact proof-source identity.

Before compilation, 5,673 external objects were checked and the imported read-only project source/object/dependency cohort was verified. `reuse.json` records 2,117 selected runjoin closure modules, and `decoder-reuse.json` records eleven rj4idb modules with byte-identical candidate sources and accepted objects. Pre-audit native03 checks **2,069** actually consumed closure objects; post-audit native04 checks **2,072**, with **zero mismatches**, and rechecks all 5,673 external objects. The three new audits are focused source/model checks; 66299 is the single final diag9 manifest, not the frozen privacy-release manifest. No unchanged full regression was run.

Rejected Lean: 66215 missing Outer30 namespace opening; 66216 an incorrectly qualified generated namespace, causing the entire combined open command to fail; 66236 premature unfolding under local lets in the frame theorem; 66249 reserved binder `prefix`; 66267 unreduced recursive zero/stop branches before arithmetic; 66270 dependent case substitution requiring reflexive branch witnesses; 66277 noncomputable proposition equality in a tiny model obstruction; 66278 missing Decidable synthesis through the named event predicate; 66296 missing codomain annotation in the catch-control example. Corrected predecessors pass at 66217, 66237, 66250, 66268, 66271 and 66279 respectively. The final failed example was excluded: Scope is restored byte-for-byte to accepted 66295. No rejected source was resubmitted unchanged.

Native01 rejected the scanner's handling of deployed cfg attributes on unit error variants. Native02 uses a corrected, hash-distinct scanner that explicitly checks those attributes and the deployed prover scope. Native03 and native04 accepted the closure/identity checks. Setup-time import parsing was corrected before any project-dependent compile: ignore nested Lean comments, handle multiple import names and allow recorded implicit imports. These are private scanner/input fixes, not changes to the shared launcher, source authority or proof toolchain.

`cleanup.json` records removal of only twelve private compiler products after all checks. Shared/cached objects, source snapshots, receipts and read-only links are retained. No key was created, unlinked, burned or deleted; no funds or live authorities were touched.

Stop: **Lean budget exhausted**. The next concrete deliverable is the existing runjoin step-(2) complete per-attempt producer and a complete honest native public-check cone law, followed by actual public error-site/operand/constructor-frame and adaptive request-history association. Only those native producers can discharge the three DIAG acquisition Props and the deployed V400 instance; generic criteria do not do so.

## Commits

`e803cc2fdd Derive complete-Result panic exclusions and adaptive diagnostic criteria`

The final evidence-only commit records these receipts and the completed report. No push or merge.
