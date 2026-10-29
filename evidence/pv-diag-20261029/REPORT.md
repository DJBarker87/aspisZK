# PV_DIAG — LOG D425: client diagnostics

**D348 client diagnostic coverage remains OPEN. The requested universal public-only result and exhaustive three-way classification were not established. No checked witness-dependent diagnostic FINDING was established either.** Unclassified data flow is not a counterexample. No privacy-headline premise was removed, and no implementation/model/trust condition was weakened.

Branch `codex/pv-diag-20261029`, exact sparse worktree `/Users/dominic/ZK/.worktrees/pv-diag`, candidate/base `cae2a45ae2`. Host directory `/home/dombarker/project-offloads/codex-pv-diag-20261029/`. Only this evidence directory was changed. No edits under `crates/` or `programs/`, simulator/observer edits, new Lean definitions, XR imports, Kani runs, wallet operations or key cleanup. T remains exactly `entropy_law`, `entropy_kernel`, `observation`. Side channels, including diagnostic occurrence, retry counts, timing, OOM and crash reports, remain in scope.

## Target and evidence classes

The reused deployed client is `devnet_spend`, SHA256 `fa888460b2c37bee087afd6289cd55219fe2732ea1e1c75011147ed15c260348`, 2,619,224 bytes, x86_64 Linux, rustc **1.94.1** (`e408947bfd200af42db322daf0fadfe7e26d3bd1`), LLVM 21.1.8. Build: `tools/r1-cost-probe`, `r1p-check,aspis-r1-cost-probe/ct-host-prover`, release opt-level 3, debug assertions/overflow checks off, panic unwind. The inherited build used `RUSTC_BOOTSTRAP=1` and an emission wrapper; this is recorded, not silently replaced with a different compiler configuration.

`source-identity.json` checks all **551** inherited project build inputs against git blobs at the candidate; `host-source-identity.json` checks the reused host source snapshot against the same hashes. All match. Root `Cargo.toml` and `Cargo.lock` also match the inherited additional-input record (SHA256 `3de458ef…` and `c6e47137…`). No new release build was run. `resolved-build-units.json` retains **488 Cargo fingerprint records**, including each recorded unit's resolved features and profile. This is a retained-unit inventory, not a claim that every unit is linked. The selected prover crate resolves `ct-host-prover,default,private-leaf-salts,prover,r1p-check`; anyhow resolves `default,std`.

Evidence classes:

* **Compiled-corpus/source inspection:** sink candidates, raw local CFG terminators, error constructors, exact source guards, symbols and disassembly transfers. This is not extraction refinement, a complete call/effect graph, or a noninterference theorem.
* **Finite native validation:** twelve public invalid-request executions of the byte-identical release image. These validate environment precedence on two concrete error/panic paths, not honest-input coverage or a universal statement.
* **Inherited scoped evidence:** b3p6 resume7's op227 panic-only exclusion and RDEAC's local allocation/path results. No broader closure is inferred.

No result is labelled `structural (K-1 substitute)`: no complete-Result owned-reference law and matching native differential were established here. No extraction was performed; (x') was respected by using deployed 1.94.1 native evidence, without substituting an extractor/toolchain. Compiler/sysroot adequacy remains a deployment obligation.

## Mechanical inventory and its precise limitations

The 46 disjoint scan partitions inspect **826 corpus entries**: 412 MIR, 412 dependency/root LLVM files, and two embedded std/alloc LLVM archives. **Two MIR entries fail their recorded hashes and are excluded**, leaving 824 matching entries. `input-pin-mismatches.json` gives both expected/actual hashes:

* `libsecp256k1-5923482f8c707be4.mir`: expected `fca89d5195147dfd71319385609498781281b078bf986804824f8f65c1998a52`, actual `e47244ba9c4df3360c8fa81a71bccfc009cac5aa17be93ea18616b8d47ec0d9e`.
* `libsecp256k1-75c27e421895d7c1.mir`: expected `a524eea65aa534fefa1b49f94878677a586f8c6515ab2bb03679508a1ed0090e`, actual `6fadd4886d7ab42faa2c06cb34e2fdfd9a07e8e57a874845e871f1efe5cded5d`.

The inherited wrapper deliberately omits MIR emission for libsecp256k1. These retained files therefore cannot be presumed to belong to the successful release emission. Its matching LLVM entries are retained; stale MIR is not credited or silently substituted. This job does not determine when those MIR files changed.

`stdlib-authority-check.json` additionally verifies the scanned compressed std/alloc files against their committed archives and the inherited uncompressed IR hashes. This authority comparison was performed **after** scanning and is explicitly recorded as supplemental, not a pre-scan check.

`shard-00.json.xz` through `shard-45.json.xz` contain **141,579 candidate rows**, including unlinked generic bodies and overlapping categories. They retain file/line, enclosing function, basic block, instruction, and a reference to that function's raw local branch/return terminators; inline scope annotations and Result-return signatures are separate arrays. `client-sites.json.xz` indexes the **879** rows in the root crate's MIR/LLVM units, including monomorphized/inlined dependency code. `image-sites.json.xz` records **12,759** candidate machine transfers/syscalls; `image-symbols.txt`, `dynamic-imports.txt` and `image-disassembly.sha256` identify the corresponding image analysis.

| Corpus category | Candidate rows (overlap allowed) |
|---|---:|
| stdout / stderr | 407 / 56 |
| write candidates / log candidates | 4,218 / 463 |
| returned error constructors | 24,828 |
| panic / hook candidates | 86,534 / 6 |
| backtrace / diagnostic formatting candidates | 207 / 459 |
| indirect calls / inline assembly | 23,014 / 1,405 |

**This is not the enumeration of every actually reached diagnostic sink required by item (1).** Name matching is a conservative discovery mechanism, not a proof that fully lowered/inlined effects, indirect callees, foreign libraries and OS crash reporters are completely covered. Conversely, candidate membership does not prove reachability. Raw CFGs give local trigger expressions, not a transitive public/witness provenance proof. Formatting/allocation precursors are distinguished from actual emission. The following source-reviewed table adds implicit runtime entries, including `Termination::report`, which cannot be inferred merely from an `_eprint` search.

## Sink table and honest-run classification

The required three-way partition cannot honestly be completed: **UNRESOLVED** below is an open obligation, not a fourth successful security classification. Source references/guards are in `source-triggers.json`, root compiled sites and the copied std/anyhow sources. “Constant text” always means conditional on selecting that error/site; it does not classify occurrence.

| Sink / precursor | Exact trigger and content | Honest-run classification / evidence |
|---|---|---|
| `main` stdout, `devnet_spend.rs:15,22` | `plan::run(&q)?` succeeds, or signing/serialization succeeds; prints one JSON value. The prove result contains `attempts`, `attempt_index`, `prove_wall_seconds`, `mask_audit`, selected account and protocol payload (`plan.rs:129`). | **REACHED on successful route; global public-only content/occurrence UNRESOLVED.** Protocol payload and timing/count observations remain covered obligations. Audit fields alone are fixed by success guards, as discussed below. |
| Client returned errors and `Termination<Result<_,anyhow::Error>>::report` | Any propagated `Err` in `main`; std `process.rs:2609–2618` attempts stderr `Error: {err:?}` and returns failure. Stderr I/O errors are ignored by this reporting helper. | **UNRESOLVED** for all honest post-preparation failures. A successful `main` result does not enter this match arm; this source fact is not a proof that every honest run returns success. |
| `plan::err` (`plan.rs:21`, prover call at116) | `.map_err(err)` receives an error, formats `"{e:?}"`, constructs `anyhow::Error`. Prover `verifier::Error` has eleven payload-free variants. | Selected unit variant has fixed spelling; **occurrence/variant selection and captured frames UNRESOLVED**. Foreign decoder/compiler/signing error types need their own payload analysis. |
| Client `ensure!`/`anyhow!` | False public-account/canonicality/length/settlement/checkpoint/anchor guards; unknown action; exact literal messages retained in source inventory. These client uses provide explicit messages. | Literal content established by source inspection. **Complete public-only classification UNRESOLVED** until guard operands and domain are bound to the public projection. Pre-preparation failures cannot simply be excluded from a whole-run claim. |
| Generic `anyhow::ensure::render` | Fancy comparison ensure fails; `Debug(lhs)` and `Debug(rhs)` are rendered and their lengths contribute to capacity. This is distinct from the explicit-message fallback used by the reviewed client ensures. | **UNRESOLVED** dependency/inline caller and operand provenance; RDEAC did not provide a universal caller exclusion. |
| Internal retry error values | Mask sample exhaustion, `ActivePole`, or false P_R1 becomes unit `Rejected`; `retry_attempt` catches it and recurses. At `k>=8`, constructs `AttemptsExhausted`; any other `Err(e)` aborts immediately. | **Constructed error values are reachable in the retry control design.** The reviewed retry function contains no print/log/anyhow conversion for an individual rejection. Whole-attempt callee effects and witness-independent occurrence/count law remain **UNRESOLVED**; no claim that an honest attempt never constructs an error. |
| Nonce-store diagnostic state | `reserve_fallible` gets I/O error; `reserve` sets `last_error=Some(error.kind())`, returns false. Existing file gives `Ok(false)`; it is not logged there. Open errors before proving propagate as `io::Error`. | Retained state and returned errors remain observable obligations. Callback-count/path/failure-event independence **UNRESOLVED**, including option-B failure repair. No key/nonce files were created by this job. |
| Dependency log macros / logger dispatch | Reaching enabled log macro/call, subject to level/filter/logger state; formatted arguments and any logger's output selection. No log macro appears in the reviewed client entry sources. | **UNRESOLVED** for the dependency/foreign cone. Lack of a client logger installation is not promoted to a whole-image silence proof. |
| `_print`, `_eprint`, std `print_to` | Requested write occurs; `write_fmt` fails => panic `failed printing to {label}: {e}` (`stdio.rs:1155–1166`). | **UNRESOLVED** honest I/O failure occurrence and selected error; strerror/error code may influence content. |
| Panic payload / default panic hook | Bounds/assert/unwrap/explicit panic or runtime failure; hook prints thread name/OS id, location and string payload, with fallback behavior. Frame printing rules below. | **UNRESOLVED** globally. Public malformed requests demonstrate reachability only outside successful canonical preparation. Successful preparation alone does not prove absence of all downstream assertions/OOM. |
| op227 formatting | b3p6 resume7 found formatting only on its panic path; honest successful path excludes that path. | **NOT REACHED on the scoped honest op227 path**, reusing the prompt's inherited evidence, not re-proving it here. This does not exclude other panic/format sites. |
| Default allocation-error hook / `rust_oom` | Failed allocation reaches handler; prints `memory allocation of {layout.size()} bytes failed`, may emit a trace, then aborts. Repeated failure suppresses trace to avoid recursion (`alloc.rs:355–431`). | **UNRESOLVED** on honest runs with environmental allocation failures. Requested size and the selected call stack need public provenance. Default OOM does not unwind, but it is not silent. |
| `Backtrace::capture` / existing backtrace reuse | Anyhow error constructors or another caller reaches capture/request; environment cache controls capture; existing provided backtrace can prevent a new capture. | **UNRESOLVED** honest entry, error-provider and frame provenance. Enablement alone is environmental; reaching capture and stack selection are control/data dependent. |
| Backtrace symbolization | Captured trace is formatted (anyhow ordinary Debug, panic/OOM hook, other caller); selected PCs drive frame/module/unit/cache selection and build-id/debuglink/debugaltlink/split-DWARF/addr2line work. | Artifact metadata is public; **selection, number/order of operations and resulting strings UNRESOLVED**. Public metadata does not make selected frames public. |
| `strerror`, UTF-8-lossy, `fmt::estimated_capacity` | Selected OS error is formatted; selected invalid UTF-8 bytes are converted; formatting invoked. Capacity estimate depends on literal template shape, whereas fancy ensure and later buffers also use operands. | These are **precursors**, not necessarily emissions. Their selected inputs/guards and eventual emitted content are **UNRESOLVED**, as in RDEAC. |
| Fatal runtime, foreign writes and crash reports | Fatal handler/abort/signal/foreign callback reaches stderr or a configured crash reporter; reporter may include PCs/registers/memory. | **UNRESOLVED**. Dynamic imports/indirect sites are retained; no OS crash-report configuration, report-content law or complete foreign-effect closure was established. |

## Exact backtrace rules in this build

The deployed lock and MIR identify **anyhow 1.0.104**, features **default,std**. The optional Cargo `backtrace` feature is not selected. In this version `std` itself enables `std::backtrace::Backtrace` and `backtrace!()` calls `Backtrace::capture()`; there is no inference that absence of the optional Cargo feature disables traces. Build output enables `error_generic_member_access`: conversions using `backtrace_if_absent!` first ask whether the source error provides a backtrace, and capture only if it does not. Ad-hoc `Error::msg`/formatted-message paths request capture. Wrapping an existing anyhow error can retain its earlier trace rather than obtaining a trace at each `?`.

The installed std has working backtrace support, confirmed by linked code and the finite controls. `Backtrace::enabled` (`std/backtrace.rs:253–273`) caches its first decision in a process-wide atomic:

1. `env::var("RUST_LIB_BACKTRACE") == Ok(s)` selects `s != "0"`.
2. On an error reading that Unicode variable (including absent/non-Unicode), it consults `RUST_BACKTRACE` with the same comparison.
3. If both reads error, disabled. Empty or other non-`"0"` Unicode values enable it.

`capture()` returns Disabled if false; otherwise it records the current stack. `force_capture()` bypasses this environment check; `disabled()` records no stack. No claim is made that every possible dependency caller uses only `capture()`.

Anyhow ordinary `Debug` formatting prints the message and cause chain, then the captured backtrace; alternate Debug returns the underlying Debug representation instead (`anyhow/fmt.rs`). Std `Termination` uses ordinary `{:?}`. Capturing and symbol resolution are separate: formatting a captured trace triggers lazy resolution and the RDEAC-selected ELF/DWARF machinery.

The default panic hook separately reads/caches `RUST_BACKTRACE` through `get_backtrace_style`: `0` => off, `full` => full, other set values => short; unset => platform default (off in the tested Linux image). `RUST_LIB_BACKTRACE` does not control that hook. `force_no_backtrace` suppresses a trace; a double panic forces full otherwise. The default OOM hook uses that panic backtrace style, with its own previous-allocation-failure recursion guard.

**Environment-only enablement is not environment-only capture occurrence or content.** A constructor/hook must first be reached; existing-backtrace provision and the stack at that point also matter. `compiled.trace` flows through `lean_copy_row_values`/`no_pole` and `ct_pole::all_slots_clear` to an `ActivePole` branch. Thus witness-derived data participates in an error-time control predicate. This source data-flow observation is not a checked pair of honest same-public inputs, nor proof that the allowed joint diagnostic law changes with the witness. That relational/distributional obligation remains open.

`backtrace-finite-validation.json`: six environment settings on each of (a) unknown public action returning anyhow error and (b) public `null` request panicking on malformed shape. All twelve expected trace-presence results matched; exits are respectively1 and101, stdout empty. No secrets, keys, proof preparation or proving were involved. These checks cannot establish honesty, retry privacy, universal hook coverage or absence of a witness-dependent trace.

## Honest preparation and retry analysis

`RealR1_client::prove_for_proof_accounts` chooses S2 and maps entropy-generation failure to unit `Entropy`. Only `Rejected` retries; errors from entropy, reservation/layout, semantic checks, commitment/proof construction and other non-Rejected sources abort. A rejected attempt constructs an error value even when no error reaches the outer API. Eight consecutive rejections expose `AttemptsExhausted` through `plan::err`, `main` and stderr. Eventual success exposes the successful attempt count/account and elapsed time on stdout.

The three rejection sources have different dependencies:

* P_R1 receives `R1PublicChallenges`; its predicate reads those challenges, not `compiled.trace` directly. A public-only predicate does not by itself prove a witness-independent distribution of its FS inputs.
* Mask-decode exhaustion arises from the secret expander/entropy path. Its source and joint retry law must be related to the public-coin simulation.
* `ActivePole` is derived from witness trace copy-slot values and challenges. Its existing rare-event bounds/transport must be composed with actual retry and diagnostic observations; simply claiming no rejected proof bytes are published is insufficient.

`mask_audit` is not an established leak. Before a successful return the source requires counts16 and10 and three inactive-balance booleans true; it separately requires `h1_total_balanced` true. Therefore successful returned audit fields are fixed by explicit guards. This is source inspection, **not a new Lean/native serialization theorem**, and says nothing about whether or when failure occurs.

`source-model-review.json` records the inspected existing Lean declarations. `ProverRwRetryModel.retry` transports returned Result/status/store through `ProverCommitRetry34.run`. The latter's older `published` projection erases the attempt count; the actual client prints that count. These models do not expose `main`/`plan::err`, std `Termination`, stderr effects, panic hook or captured frames as the diagnostic observer trace. Proving that a pure Result model has no logging operation would not prove native silence through its external dictionary. **No honest-run silence theorem was added or claimed.** Successful canonical preparation does not alone discharge all later entropy, allocation, filesystem, rejection and proof-stage effects.

## AGENTS section 6 receipts, failures and budget

`attempts.json` contains the exact target/command, admission, exit, GNU-time wall, peak RSS, swap, source revision and script SHA for every scope; raw `nativeNN-{receipt.json,time.log,output.log}` and `admission-nativeNN.{json,log}` are retained. Each script SHA is linked to its committed version. Target project source identity is separately pinned to the candidate. `#print axioms`: **N/A for every scope** (native analysis/execution, no Lean theorem). There are **zero Lean attempts**, no Env-J IDs used (62400–62499 and audit62497–62499 remain unused), and **zero Kani**.

Exactly **50 capped scopes**, 48 exit0 and two exit1, total outer scope wall **341.097s**, peak RSS **231,916 KiB**, all swaps0. One own scope ran at a time; all used MemoryHigh6G, MemoryMax8G, MemorySwapMax0, TasksMax64 and timeout900. Expected work was recorded as corpus/source analysis; no unoptimized arithmetic, proof generation, cold dependency build or regression replay occurred. No full frozen manifest was run because there is no new proved endpoint to replay.

* `native14`: exit1 at the first retained MIR hash mismatch. Its input failure is retained. Revised scanning explicitly excludes and records mismatches; the affected two input partitions were processed together under `native15`, not retried unchanged or given a larger cap.
* `native48`: exit1 before executing any client because the inherited baseline file is not executable. `native49` uses a private byte-identical executable copy, completes the twelve controls, then analyzes the image in the same sequential scope. No other job's file mode or contents were changed.
* `native50`: final aggregation exit0. The native scope allowance is exhausted. The Lean allowance remains unspent; no claim that the entire authorized Lean budget was exhausted.

Admission was checked in the same wrapper invocation that launched each scope and required **exit0 AND allowed:true**. All50 admission receipts meet this; zero refusals/cooldowns/void attempts were observed. No claim is based on an earlier reservation snapshot. The first audit script and subsequent revisions are preserved by git; execution targets and revisions distinguish them. Native49/50 were invoked after the historical batch stopped at48; actual commands in receipts are authoritative.

No generated binary, .olean, ELF or archive is committed. The private executable copy is removed after evidence collection. Every committed file is below20MB. Sparse paths were added with `git sparse-checkout add`; no full checkout occurred. Stage commits appear in `COMMITS.txt`; the final evidence commit adds this report and receipts. Nothing was pushed or merged.

## Premises retained and exact next deliverable for D348

Before/after: **unchanged** global client diagnostic occurrence/content obligation at `PrivacyR1HeadlineDeployedReal.privacy_headline_deployed` and its D159/D348 deployment conditions; no premise removed, added, folded into T or weakened. RDEAC's V178/V181 global diagnostic-provenance blockers remain retained; local path/allocation results are not upgraded to global diagnostic closure. The privacy target is not yet established.

The owner still needs answers/evidence for these concrete questions:

1. What is the authoritative complete linked sink/effect closure, including inlined std, indirect/foreign callees and the configured OS crash reporter? Repair/replace the two unbound MIR artifacts or supply an explicit LLVM/source completeness argument. Names, symbol absence and the present conservative inventory cannot discharge this.
2. For every post-canonical-preparation error, can its guard be proved impossible, or can its **joint** event/error-code law be transported to public data and simulator coins? In particular include pole rejection, exhaustion, entropy/I/O failure, later semantic errors, allocator failure and print failure. Preserve option-B's witness-independent failure requirement.
3. Do the existing pole/exhaustion bounds already cover the now-observed retry/error-stage/frame distinctions, or is a further observer-transport proof required? A per-event mass bound is not automatically a joint-observer proof. No observer/simulator change was made here.
4. For each surviving error, which Debug/Display/ensure operands reach `main` or another client API? Prove selected error strings/lengths and invalid-UTF8 guards public; a constant enum spelling only resolves payload conditional on its variant.
5. When captures are enabled, can the selected error-time stack/PC/module/unit/cache/metadata accesses be proved public on honest runs, or included in the existing permitted joint simulation/bound? Disabling traces in one test/environment is not a universal theorem over deployed environment handling.
6. Supply a source-faithful diagnostic effect model and native binding that consumes the retry Result model without erasing attempts, errors, panic/OOM or frames. Then prove the per-sink honest-run silence/public-content statements and audit their axioms under fresh authorized IDs.
7. Compose that result at the actual deployed client/RunJoin endpoint and perform one coherent closure replay/axioms audit. No owner decision may replace these P obligations with another T field.

The immediate next deliverable is a **complete client error-exit and capture-site provenance certificate with a diagnostic-effect refinement**, beginning with the returned-error-to-`Termination` path and the `ActivePole`/retry/exhaustion surface, using the inventory here as discovery input. This job stops with its50 native scopes spent and these exact proof/coverage gaps retained, not with a positive D348 answer.
