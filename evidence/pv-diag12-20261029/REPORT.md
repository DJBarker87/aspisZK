# PV_DIAG12 — D474

**Target not yet established. The requested complete syscall-boundary binding and complete JSON/stdout Step and Readout were not discharged. No deployed Link was closed and no endpoint premise was removed.**

Worktree exactly `/Users/dominic/ZK/.worktrees/pv-diag`; branch `codex/pv-diag12-20261029`; base `b1aad8357f`. Continued the prompt's option (A) proof work while retaining the owner's adopted **option B OS-failure treatment**. Those are different uses of “option”; no environment-availability assumption was substituted. No owner response or client change was inferred.

All fifteen original `PV_DIAG10_Link_*` definitions are byte-unchanged, checked against the base in `link-definition-integrity.json`. All three typed DIAG acquisition skeletons remain unchanged and conditional. The observer, simulator, original charged union, error bound, and capped T (`entropy_law`, `entropy_kernel`, `observation`) remain unchanged. No crate/program/release pin/key/wallet/account/nonce was edited, created, discarded, or operated on. No push or merge.

## What this round actually establishes

The eight `PV_DIAG12_` proof modules replace some former whole-call trace parameters with explicit **POSIX ABI request/reply interpreters**, used generically by the file-descriptor and buffering operations. They are mathematical/source-control results, **not complete transitive own-1 bindings of the deployed operations to kernel syscalls**. Each of the nine source-body association records in `primitive-bindings.json` deliberately has `complete_syscall_binding:false`. A checked source excerpt/token occurrence is not being credited as a universal native refinement or a completed structural gate.

- `Boundary`: explicit write/open64/close requests retain fd, pointer base/offset, bytes, clamped count, flags/mode, and replies. `bind_prefix`, `bind_assoc`, `requested_append`, and `delivered_append` prove composition without erasing request/reply prefixes.
- `Fd`: Linux x86_64 `READ_LIMIT = ssize_t::MAX`, one write ABI request, ordinary File/raw-stdio flush returning Ok without fsync, and a close body ignoring its result without retry. **The close model requires the UB-check probe to be disabled; this specialization is not established merely by citing the release profile.** The enabled source branch can call fcntl and abort.
- `Fd`/`WriteAll`: scalar stdout/stderr EBADF handling is separate from delivery. `std_ebadf_accepted` and `std_ebadf_not_delivered` show why successful acceptance cannot be equated with bytes delivered. `stdWriteAll` masks EBADF around the *whole* inner write_all loop, matching the source; it does not mask each inner write. EINTR consumes the next boundary outcome while retaining the same remaining slice; positive writes advance both byte view and pointer offset. Zero, other errors, invalid count, and missing returns have separate model branches.
- `Open`: access/creation-mode validation and open_c request shape, including CLOEXEC, access-mode masking from custom flags, mode, and cvt_r's EINTR retries. The validation result identifies which source error must be constructed; it does **not** silently prove that allocation/error construction is total or effect-free. Path/CStr conversion and constructor/cleanup associations remain open.
- `Buffer`: strict fast-path capacity test, buffering, direct writes, flush-loop progress and EINTR/error/zero branches, panicked state, drop's ignored returned error, and normal-return content rebasing after draining. `flushLoop` represents the remaining view; `flushBuf` restores the original buffer coordinates on ordinary return. Actual Vec memory moves, live BufGuard state, borrowing, unwind and in-flight memory are not proved by this content model.
- `Line`: last-newline scanning/splitting and the ordinary `LineWriterShim::write` and `write_all` cases, including old-buffer flush, empty/nonempty buffering paths, partial writes, tail selection, capacity and buffering decisions. `lineSpan_tail_content` proves the symbolic split preserves all bytes. No large concrete normalization was used.
- `JSONStdout`/`Composition`: one supplied serialization fragment sequence followed by one supplied newline span. `jsonStream_error_stops`, `jsonStream_cut_stops`, `println_error_no_newline`, and `println_cut_no_newline` prevent later ordinary fragments/newline after error or cut. `jsonStream_append` and `onePrintln_chunks_append` prove ordered composition. `println_delivered_prefix` and `println_requests_prefix` preserve earlier effects.

**Pending-write correction:** the initial provisional model allowed only an empty delivery at a missing return. Review identified that as insufficient for an observer prefix. Final `Reply.pending visible` retains bytes already delivered before the caller observes a return, and `delivered_pending`/`pending_prefix_readout` prove their preservation. All five affected final module closures were recompiled against the changed Boundary. Earlier successful provisional snapshots remain as history and are not the final authority.

`Signal : Nat → Request → Reply` is an arbitrary boundary-outcome provider. Its cursor indexes issued boundary operations, including a pending call. Its definition proves neither publicity nor witness independence. The option-B P row remains exactly the existing obligation that the failure event is witness-independent. Pointer/capacity/length/retry provenance and the outcome policy still have to meet that P row; they are not transferred into T.

`delivered` reads returned-count-confirmed prefixes and explicitly supplied pending delivery. A native instance must establish the foreign return/count and pending-prefix contracts. The full reply is retained even for an invalid count. The model tags -1/-2 stand for WriteZero/violated Write contract; they are **not native errno, panic payloads, abort terminals, or hook executions**. A fuel cut is a finite model observation boundary, not a proof of native divergence. No theorem identifies this reduced `Result` with the complete native terminal or erases the latter.

## Why the first channel is still open

`residual-inventory.json` records the concrete obligations. The checked source is rust-src **1.94.1** and the frozen client's **serde_json 1.0.151**. Native02 rechecked all 551 frozen source inputs; no source or feature selection was changed.

1. **Foreign ABI is not the kernel syscall boundary.** Rust's FileDesc calls libc::write, open_c calls open64, and OwnedFd calls libc::close. Their libc cancellation/TLS/errno paths and exact kernel request/result expansions are not bound here. `libc-identity.json` and `libc-write-disassembly.txt` identify the inspected host library as supporting evidence only; its deployment association and semantics are not assumed. A libc ABI call is not relabelled a syscall.
2. **Lock and initialization state remain real inputs.** stdout uses OnceLock and a ReentrantLock of RefCell of LineWriter; stderr's underlying writer is unbuffered. ReentrantLock::lock obtains current_id, checks owner, checks/increments recursion count or acquires the mutex and stores owner/count. Guard drop decrements count and may clear owner/unlock. TLS/thread-id initialization, contention/spin/futex paths, overflow panic, RefCell borrowing/reentrancy, actual allocation/capacity/addresses, and native guard destruction remain unbound. Merely adding a lock label or assuming an empty buffer would not establish the requested primitive association.
3. **The actual serde fragment producer is not instantiated.** Value::fmt selects compact to_writer for `{}` and constructs WriterFormatter. Its write converts the serializer's bytes to UTF-8, invokes Formatter::write_str, and on fmt error calls `io::Error::new(Other, "fmt error")` before mapping back to fmt::Error. That allocation and cleanup cannot be erased. The recursive Serialize variants, numeric/string/map/sequence formatting, callback dispatch, fragment pointers and order remain required. `jsonStream` takes this fragment sequence as input; its ordered composition does not prove that serde produces it.
4. **fmt and print error paths still matter.** std::io::Write::write_fmt's statically-known-string branch differs from default_write_fmt. The latter adapter stores the underlying I/O error, invokes fmt::write, returns the stored error, or panics if a formatting error had no underlying I/O error. Capture/TLS/mutex branches and restoration, print_to's error formatting/panic hook, error drop, unwind, crash/OOM/register/raw-memory/final-state observations, and shutdown's try_lock/LineWriter replacement/drop remain required. The syscall model does not subsume them.
5. **No actual observer-state/native-event/readout instance was constructed.** Source-local request and delivery composition do not identify the existing complete NativeTrace events, actual returned JSON bytes, print request/delivery pairs, or all abnormal prefixes. The unchanged native decoder is reused in the final manifest; no substitute observer was introduced.

Thus **neither the deployed JSON/stdout Step nor its Readout is discharged**. Init and exhaustive EventOrder also remain open. Work did not advance to proving the other deployed channels after claiming JSON complete. File/OpenOptions and stderr equations above are shared primitive-layer work, not closure of those channels.

## Every original Link's status

All names below have prefix `PV_DIAG10_Link_`.

| Link | File channel | JSON/stdout channel | Error/stderr channel | Exact status |
|---|---|---|---|---|
| Init | OPEN | OPEN | OPEN | Existing decoder/model initialization laws retained; actual native state, buffers, capture and lock initialization not instantiated. |
| Step | OPEN | OPEN | OPEN | Explicit ABI/buffer/stream model cases proved; complete source-to-syscall, memory/store/drop/error/hook/unwind and delivery association still missing. |
| Readout | OPEN | OPEN | OPEN | Model requested/delivered-prefix laws are not equality with actual file/JSON/stdout/stderr/error/native observer values. |
| EventOrder | OPEN | OPEN | OPEN | Ordered model composition proved; complete native producer and every abnormal prefix still unbound. |

| Link | Status / ownership |
|---|---|
| Operands | **OPEN deployed.** Prior conditional unit-error producer result retained. Full reached dynamic formatter/error/logger operand producers and arbitrary Debug remain unproved. No new honest witness-dependent diagnostic was established. |
| Levels | **OPEN deployed.** Prior model initialization/selection facts retained; complete reached logger binding, setters, callbacks and mutable-state evolution unbound. |
| Frames | **OPEN.** Actual PCs, constructor/capture/hook/worker/unwind frames and resolver association remain required. No frame-publicity inference is made from an ABI trace. |
| Request | **OPEN V400.** Request fields and source-local progress are explicit; actual buffer/address/allocator/locking/entropy/I/O policy and off-original-bad provenance/publicity remain unbound. |
| ExecutionHistory | **OPEN.** Exact actual histories, syscall replies, reads, pending effects, cleanup and terminal/prefix association still needed. |
| Sites | **CONSUMED INPUT — level 1 (`pv-l1e`).** Joint occurrence/variant/site law; not worked on or weakened. |
| Entropy | **CONSUMED INPUT — runjoin and retry producers.** Complete actual entropy producer; unchanged. |
| MaskedAttempt | **CONSUMED INPUT — runjoin and retry producers.** Complete honest attempt producer; unchanged. |
| ReachedAttempt | **CONSUMED INPUT — runjoin and retry producers.** Actual reached-retry producer; unchanged. |
| WorldBlind | **CONSUMED INPUT — `pv-own` interface.** Actual world blindness; unchanged. |
| ChargedBad | **CONSUMED INPUT — endpoint bad-event predicate, runjoin step (4).** Exactly the original headline union; no additional charge. |

All three deployed `DIAG_*` acquisition inputs remain OPEN. `PrivacyR1HeadlineDeployedReal.privacy_headline_deployed` premises removed/added/weakened/changed: **0/0/0/0**. Before and after, native acquisition, original joint L1, deployed V400, actual prover/checker producers and dependency/release association remain required. V038, V178/V181, V336–V339, V347–V351, V370, E1/E2 and D381/D386 retain their prior status.

Sink dispositions: JSON/stdout/partial delivery/print panic; file/recovery/nonce I/O/read errors; returned errors/Termination/stderr; dynamic diagnostic operands; logger; native panic/crash/OOM/capture/frames/resolver/register/raw-memory/final state are all **UNRESOLVED at the complete deployed acquisition boundary**, with the residuals above and inherited DIAG11 obligations. Prior scoped canonical compiler/encoder and complete-Result panic exclusions are retained only at their established domains. No shipped privacy counterexample was established in this round.

## Validation, resource receipts, and stop

**100/100 Lean attempts**, IDs **67300–67399**, **94 accepted / 6 rejected**. **4/30 capped native scopes**, **0 Kani**. Every admitted scope recorded admission exit 0 and allowed:true. No refused admission, void launch, timeout, memory kill, cap increase, or scope overlap was observed. Caps were MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64, Lean -M7000. One scope at a time. No Rust/native client build or differential execution was performed; the four native scopes were source/cache hashing, source association checks, supporting objdump, and final evidence checks.

Each receipt records the exact target/command, exit, wall time, peak RSS, swap, source revision label, input snapshot/hash, import-object fingerprints, admission/caps and complete printed axioms (or native N/A). All **103 final new theorems** are covered by `audit-coverage.json` and the two axioms audits; accepted final axioms are subsets of {propext, Classical.choice, Quot.sound}. Maximum Lean RSS was **4,956,720 KiB**; total Lean wrapper wall **35.55 s**; swap zero. No broad normalization of a large concrete recurrence/numeral was used.

| ID | Exact target | Exit | GNU wall | Peak RSS KiB | Swap | Source revision |
|---|---|---:|---:|---:|---:|---|
| 67397 | PV_DIAG12_Audit | 0 | 0:00.17 | 476416 | 0 | d4a8aa61a1532467cb320b7c34df214efbd6cbf3 |
| 67398 | PV_DIAG12_ProducerAudit | 0 | 0:00.18 | 477268 | 0 | d4a8aa61a1532467cb320b7c34df214efbd6cbf3 |
| 67399 | PV_DIAG12_FinalManifest | 0 | 0:01.75 | 4956720 | 0 | d4a8aa61a1532467cb320b7c34df214efbd6cbf3 |

The final manifest ran **once**. It checks the unchanged three original typed inputs alongside the new source-layer modules; it is **not the frozen privacy-release replay**. The frozen runtime/adversarial/reproducible-build suites were not rerun after unrelated Lean-only work.

Rejected compiler inputs remain with their full source snapshots/output: 67303 (bind/pure simplification); 67309 (conditional simplification in delivery); 67316 (conditional simplification in EBADF masking); 67324 (Bool-to-Prop guard simplification); 67362 (new pending-empty delivery branch needed case simplification); 67363 (attempted positive/negative conditional lemmas with incompatible proof types). Each was changed before the next submission. `finalize.py` checks that no failed source hash was submitted again. Recompiling accepted dependent sources at 67365–67368 was justified by the changed pending-delivery Boundary object, not an unchanged regression.

Native01 checked all **5,673 external objects** and the **2,161 reused project/source objects before the first Lean attempt**, using inherited pinned cohort authority without replacing shared files. Native03/04 independently checked them again, plus current final import fingerprints, all frozen final source/object associations, standard-library/dependency snapshots and accepted input identities, with zero mismatches. The same private coherent cohort is reused read-only; no b3p cohort was combined here. `resolved-features-reused.json` retains DIAG11's successful locked/offline **399-crate** feature/dependency metadata evidence and checks the current frozen Cargo.lock hash. Metadata is not a release rebuild or proof of syscall association.

`freeze-sources.json` binds all eight proof modules and three audit/manifest modules to proof-source commit **d4a8aa61a1532467cb320b7c34df214efbd6cbf3**. `proof-source-commit-binding.json` connects their git blobs to final accepted submitted snapshots. Initial receipts' `b1aad8357f...` revision fields name launch context; they do not attribute dirty proof text to that clean revision. The snapshots/hashes identify compiler inputs. `verification-final.json` and `summary.json` record the final check. The generator's final sources match all eight final modules exactly.

**Stop: Lean budget exhausted.** The shared blocker was made explicit at reusable ABI-request granularity, but the requested exact syscall-boundary and deployed first-channel closure remain unfinished. The next concrete deliverable is the complete std/libc outcome and state association for stdout, together with the actual serde_json Value::fmt/default_write_fmt fragment/error producer and capture/lock/cleanup producer; then instantiate the unchanged JSON/stdout Step, Readout, Init and EventOrder. Only after that should work advance to the other deployed channels. No missing fact is moved into T, an availability assumption, or a new charged event.

## Commits

```text
d4a8aa61a1 Preserve pending delivery prefixes and compose streaming JSON with line buffering
8448f31206 Model Unix I/O requests and distinguish accepted from delivered stdout bytes
```

The subsequent evidence-only commit records this report, the final audits and their receipts. No push or merge.
