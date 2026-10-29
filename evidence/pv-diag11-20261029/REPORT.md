# PV_DIAG11 — D471

**Target not yet established. No complete deployed Link was discharged.** Worktree exactly `/Users/dominic/ZK/.worktrees/pv-diag`; sparse branch `codex/pv-diag11-20261029`; base `c84e5c2ef7`. All fifteen DIAG10 Link definitions and all three typed acquisition skeletons are unchanged. This round supplies source-control laws and checked source excerpts, not a complete own-1 refinement of the deployed client. It does not meet the requested end-to-end discharge.

Option B, the complete existing observer, the original charged union and error bound are retained. T remains exactly entropy_law, entropy_kernel, observation. No crate, program, simulator, observer, release pin, key, wallet, account or nonce was changed. No merge or push.

## Results, with their actual scope

`PV_DIAG11_Execution`, `WriteAll`, `Cleanup`, `File`, `Print`, `Report` and `Client` prove the local control cases for ordered calls and ordinary Result propagation. Their primitive arguments are **complete call traces**, not proof that the native calls implement those traces. Init/Step/Readout/EventOrder are not instantiated merely by introducing these models.

The checked Rust 1.94.1 source excerpts establish the following outer control associations, subject to the explicitly listed unbound primitive calls in `source-bindings.json`:

- `std::io::Write::write_all`: empty buffer returns; zero write returns WRITE_ALL_EOF; a positive count advances the slice; Interrupted retries the same slice **after destruction of the returned error**; other errors return. Each primitive call's finite prefix is retained. An oversized count exposes the slice-panic branch rather than silently saturating it. The native Write contract, error categorization/destruction, borrow restoration and panic hook are not proved by this interpreter.
- `std::fs::write::inner`: File::create, write_all, then destruction of the File temporary on ordinary Ok/Err. Creation failure does not invoke write or close. Path/content AsRef conversions, their cleanup, OpenOptions, fd/syscall forwarding and drop/unwind implementations remain unbound.
- `stdio::print_to`: a successful capture returns; otherwise global write_fmt runs. A returned I/O error invokes a separate panic/hook run, preserving its effects. It is not converted to a silent panic tag.
- `attempt_print_to_stderr`: a successful capture returns; otherwise stderr write_fmt runs. A returned I/O error is ignored **as a Result but still destroyed**. Formatting, error destruction, TLS, locking and panic can still have effects. The new laws explicitly preserve these paths.
- `Termination<Result<T,E>>`: Ok delegates to T::report; Err formats `Error: {err:?}\n`, attempts stderr, returns FAILURE after ordinary completion and destroys E. Debug, stdout/stderr buffering, allocation, error drop, unwind and native capture are not assumed total or silent.
- The source tail in `plan::prove` orders proof-file write before statement-file write, followed by all remaining instruction/account/JSON construction. `main` evaluates `plan::run(&q)?` before stdout formatting. Each `?` stops later ordinary calls. The model's `json` parameter represents the **entire** intervening tail, including its errors and effects, not an atomic JSON operation.

These are checked **outer source-control excerpts**, not a complete transitive own-1 binding and not a `structural (K-1 substitute)` gate: no same-input native differential or complete native primitive family was established here. `Exit` is a control classification, not a replacement for NativeTrace's terminal. Its tags do not supply native panic payloads, PCs or crash data; those remain required in the unchanged complete observer. No theorem in this round translates these tags into a complete native terminal. The fuel cutoff is a finite observation boundary, **not proof that the native execution diverges**.

`PV_DIAG11_Public.unit_error_operand_link` proves the ORIGINAL `PV_DIAG10_Link_Operands` for the **unit-error model producer**, conditional on a same-public error-variant law supplied by L1. It allows site, frame and level fields to vary independently. It neither proves the L1 law nor extends the conclusion to arbitrary Debug values. Deployed Debug/carrier association and every other operand producer remain obligations.

`PV_DIAG11_Public.logger_initial_disabled` and `logger_not_initialized` prove the selection/filter facts for the checked log 0.4.34 initializer and selection branch: LOGGER=NopLogger, STATE=0, MAX_LOG_LEVEL_FILTER=0; STATE unequal to INITIALIZED selects NopLogger. The source mutation sites are recorded. Absence or publicity of all reached setters, constructors, indirect callbacks and global-state transitions was **not** established. Environment configuration alone is not used as their proof.

`PV_DIAG11_Requests.writeAll_same_length_metadata` proves, by induction on the prefix bound and symbolic slice lengths, that equal initial buffer lengths give equal complete metadata/reply traces **when the write primitive depends only on length and the Interrupted cleanup producer is shared**. It retains partial writes, errors, retries and all abnormal primitive prefixes. `writeAll_metadata_public` transports a supplied public initial-length law. `write_request_size`, `write_slice_length`, `write_progress_offset` and `write_interrupted_preserves_buffer` expose the request fields. This is a source-local reduction of V400 request provenance; it does not establish equal native replies, actual buffer-length publicity, syscall size clamping, fd/offset/address/allocator-state association or the complete deployed request policy. Those premises are not transferred into T or a new bad event.

## Every Link's status

Names below have the unchanged prefix `PV_DIAG10_Link_`.

| Link | File | JSON/stdout | Error/stderr | Status / exact residual |
|---|---|---|---|---|
| Init | OPEN | OPEN | OPEN | Inherited decoder/model initialization remains proved; actual observer-state association is not instantiated. |
| Step | OPEN | OPEN | OPEN | Outer call/control cases refined; actual emissions, reads, buffering, stores, drops, error/hook/unwind and delivery steps still need their own-1 associations. |
| Readout | OPEN | OPEN | OPEN | No identification of actual files, serialized bytes, requested/delivered stdout bytes, errors or stderr with the accumulated source state. |
| EventOrder | OPEN | OPEN | OPEN | Final-write/main order is checked locally; exhaustive native producer and every abnormal prefix remain unbound. |

| Link | Status |
|---|---|
| Operands | **OPEN deployed.** Unit-error carrier link proved conditional on consumed public-variant law. Arbitrary Debug, all dynamic compiler/error coordinates, dependent formatting, logger operands and honest reachability need complete producers. No witness-dependent honest diagnostic was constructed. |
| Levels | **OPEN deployed.** Initial NopLogger/Off and not-initialized selection proved for model state; all reached bindings/setters and mutable-state evolution remain unbound. |
| Frames | **OPEN.** Anyhow constructor source and the existing normal-return restoration laws are retained; actual native PCs, inlining, constructor frames, earlier captures, hook/worker/unwind paths, module/build-id selection and resolver state/association remain unproved. Source inspection alone does not discharge this link. |
| Request | **OPEN V400.** Symbolic write-loop length/request progress proved; actual I/O/entropy/allocator request policy and off-original-bad provenance remain unbound. |
| ExecutionHistory | **OPEN.** Actual execution/history association, including reads, syscall replies, cleanup and every prefix, still needed. |
| Sites | **CONSUMED INPUT — level 1 (`pv-l1e`).** Joint occurrence/variant/site law. Not worked on or weakened. |
| Entropy | **CONSUMED INPUT — runjoin and retry producers.** Actual complete entropy producer. |
| MaskedAttempt | **CONSUMED INPUT — runjoin and retry producers.** Actual complete honest attempt producer. |
| ReachedAttempt | **CONSUMED INPUT — runjoin and retry producers.** Actual reached-retry producer. |
| WorldBlind | **CONSUMED INPUT — `pv-own` interface.** Actual world blindness. |
| ChargedBad | **CONSUMED INPUT — endpoint bad-event predicate, runjoin step (4).** Exactly the original headline union; no extra charge. |

No owned deployed link is relabelled closed by a model definition, source scan or conditional transport theorem. All three deployed `DIAG_*` inputs remain OPEN.

## Operands, frames and sink accounting

`source-bindings.json` rechecks 551 frozen project inputs, retains the 41 selected format/error sites and records 27 selected I/O-containing source lines. The inherited 463 logger candidates remain conservative candidates, not an exhaustive honest-reachability proof. The selected plan.rs:21 Debug helper accepts arbitrary Debug. Its selected prover-return error enum has eleven unit variants in the inherited source inventory, while occurrence and variant remain owned L1 inputs. BlockMismatch and AuxiliaryMismatch carry dynamic coordinates and are not OS outcomes. Canonical success excludes only its scoped compiler-error path; it is not a universal Debug-operand law.

The copied anyhow 1.0.104 constructor source is checked against the deployed dependency text. `Error::new` obtains backtrace_if_absent before construct_from_std; message construction reaches construct_from_adhoc with backtrace capture supplied at the caller. This identifies source boundaries, not the captured native PC list or resolver association. Returned normal callees no longer contribute live frames at the later caller, but earlier captured objects/effects are not erased. Opaque callbacks, workers, TLS/hook state and native unwinding remain open.

| Sink | Disposition after this round |
|---|---|
| Unit returned error spelling / selected literal diagnostics | Model content public conditional on L1 variant/site; deployed acquisition, allocation/Debug/delivery OPEN. |
| Dynamic compiler/error operands | UNRESOLVED outside the original successful canonical-preparation scope; no new FINDING. |
| Logger macros | UNRESOLVED actual binding, reached state and operands; initial Off alone is not a whole-run exclusion. |
| File/recovery/nonce I/O, writes and read failures | UNRESOLVED complete native acquisition and V400 request provenance. No recovery data or actual key was exported or operated on. |
| JSON/stdout, partial delivery, print panic | UNRESOLVED complete acquisition; source order/failure-control refinements proved locally. |
| Returned errors / Termination stderr | UNRESOLVED actual acquisition; source reporting/ignored-I/O-error/drop distinction retained. |
| Backtrace, constructor frames, resolver, native panic/crash/OOM/register/raw-memory/final state | UNRESOLVED actual source/native associations. All original observer channels and prefixes remain required. |
| Earlier canonical compiler/encoder scoped panic exclusions | Retained at their original domains; no expansion to whole prover/checker cones. |

`PrivacyR1HeadlineDeployedReal.privacy_headline_deployed` premises removed/added/weakened/changed: **0/0/0/0**. Before and after, actual native acquisition, original joint L1, deployed V400, actual prover/checker producers and dependency/release association remain required. V038, V178/V181, V336–V339, V347–V351, V370, E1/E2 and D381/D386 retain their prior status.

## Validation and limitations

The deployed source selection is devnet_spend; r1p-check and aspis-r1-cost-probe/ct-host-prover; release; Rust 1.94.1. Native02 ran locked, offline Cargo metadata on the frozen source and recorded resolved feature lists and dependency edges for **399 crates** in `resolved-features.json`, checking that Cargo.lock did not change. This was metadata only, not a binary rebuild or execution. Standard-library snapshots are byte-checked against rust-src 1.94.1; log 0.4.34 and anyhow 1.0.104 snapshots are byte-checked against the deployed dependencies. The source-to-machine-code boundary remains V370 / D381 / D386.

**100/100 Lean attempts**, IDs **67000–67099**: **97 accepted / 3 rejected**. **3/30 capped native scopes**, **0 Kani**. No memory kill, timeout, cap increase, refused admission or void launch. One scope at a time; MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64; Lean -M7000. Each admission had exit 0 and allowed:true. All final module theorems have printed axioms within {propext, Classical.choice, Quot.sound}.

Rejected compiler inputs: 67010, invalid nested case-alternative syntax, corrected at 67011; 67044, missing Boolean conditional simplification, corrected at 67047; 67087, ill-typed unparenthesized/adjacent notation in the logger statement, corrected at 67088. Failed snapshots and full outputs remain. No failed compiler input was rerun unchanged. An intermediate Python edit was malformed; the subsequent stale-plan dispatch was stopped by the failed-source hash guard **before admission or compilation**. It did not consume an attempt or provide evidence. Sparse git-add and generator corrections are recorded in `setup-notes.json`.

Initial compiles 67000–67078 relied on inherited external authority but lacked this job's independent live external-object check before those compiles. **This is recorded as a process omission, not presented as a timely preflight.** Native01 independently checked all 5,673 external objects before 67079. Each final module was then meaningfully extended and compiled in dependency order under the verified environment (67079–67096), followed by the audits. The final nine module sources and three audit/manifest sources match proof freeze `4e70bdb32dd82f82b0d01b4a45c58bd8fbd500a5`; `freeze-sources.json` records source SHA-256 and git blob identities. Earlier receipt revision labels identify launch context; submitted snapshots, not dirty-source attribution to those revisions, identify compiler inputs.

Native02/03 independently recheck 2,149 reused project objects/sources, 5,673 external objects, accepted snapshots, final-source identities, and current direct dependency fingerprints with zero mismatches. The inherited recursive cohort authority is retained in `reuse.json`; no b3p cohort is combined here. The pinned private cache is retained under AGENTS resource rule 6 for the unfinished obligations.

The final manifest ran once. It is a focused DIAG source-control manifest, **not** the frozen privacy-release replay. No unchanged full regression was run. The source generators reproduce all nine final module files and their snapshot plans exactly (`generator-check.json`). No broad reduction of a large recurrence or numeral is used.

| ID | Exact target | Exit | GNU wall | Peak RSS KiB | Swap | Source revision |
|---|---|---:|---:|---:|---:|---|
| 67097 | PV_DIAG11_Audit | 0 | 0:00.18 | 475716 | 0 | 4e70bdb32dd82f82b0d01b4a45c58bd8fbd500a5 |
| 67098 | PV_DIAG11_ProducerAudit | 0 | 0:01.11 | 2624504 | 0 | 4e70bdb32dd82f82b0d01b4a45c58bd8fbd500a5 |
| 67099 | PV_DIAG11_FinalManifest | 0 | 0:01.79 | 4955128 | 0 | 4e70bdb32dd82f82b0d01b4a45c58bd8fbd500a5 |

All **92 final new theorems** are covered by these audits. Maximum Lean RSS: 4,955,128 KiB; wrapper wall total 38.90 seconds; swap zero. Each committed receipt retains exact command, target, source snapshot/hash, import-object fingerprints, admission, resource caps, revision label, exit, wall/RSS/swap and complete printed axioms. `summary.json` and `proof-source-commit-binding.json` bind all final sources to the proof freeze.

**Stop: Lean budget exhausted.** The next concrete deliverable is the complete deployed I/O/formatting/cleanup primitive association and actual observer readout/event-order producer, including stdin/read errors, capture/TLS/buffering, File/OpenOptions and fd/drop/unwind paths. Then discharge the full dynamic operand and logger-state producers, native PC/resolver association, and actual off-bad request policy. No conditional model result from this round is credited as an endpoint premise removal.

## Commits

```text
4e70bdb32d Preserve interrupted-error cleanup and prove write request metadata transport
a763cf225d Add source-control branch proofs and preserve destructor effects
```

The final evidence-only commit records this report and receipts. No push or merge.
