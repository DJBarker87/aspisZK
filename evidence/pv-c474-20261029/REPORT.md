# D491 / D474(C) experimental draft — NOT ADOPTED

Branch `codex/pv-c474-draft-20261029`, base `a9a9781f8a`. No merge, push, repin or adoption. This draft changes the host client only. Privacy target not yet established; no endpoint premise removed. The complete D159 observer and D478 timing obligation remain.

## Source design

A literal-only client error carrier replaces anyhow at the client boundary; all foreign errors are discarded without Debug/Display. A constant panic hook and a host-only abort profile replace default panic reporting. Startup disables and primes std's backtrace cache before input processing. getrandom 0.3.4's supported `linux_raw` backend is selected by the client build recipe, using inline-assembly getrandom(2), without dlsym or libc getrandom. The suggested `linux_getrandom` backend still calls libc::getrandom and therefore does not remove LD_PRELOAD interposition; this draft deliberately uses `linux_raw` instead.

Validation details and costs follow below.

## Exact change inventory

`PATCH.diff` is the complete production-source/build-recipe diff against the base (evidence and test tooling excluded). No crate or program source changes. The changed files are the standalone tool manifest, its explicit build recipe, the runner, planner, account-policy helper and new diagnostics module.

- `devnet_spend.rs`: replace anyhow Result with literal-only Error; stdin, JSON parsing, blockhash parsing, message compilation, transaction construction and serialization errors map to `client operation failed`. Replace Result-returning main's automatic Debug termination with ExitCode and the constant `client error\n` stderr request. Existing TxV1 size ensure retains its literal.
- `plan.rs`: remove generic Debug-bound `err` and `anyhow!("{e:?}")`. All existing map_err sites now discard the operand without a formatting bound. Add explicit fixed mapping at SYSTEM/TOKEN/LOADER parsing, directory creation, recovery-file open/serialization/write/sync, nonce-store open, proof/statement writes and nullifier-marker address derivation. Errors already returned by Accounts are the same literal-only type. All seven planner ensure/anyhow call sites have literal operands; no formatted operands are permitted by the replacement macros.
- `Client64_accounts.rs`: use the same literal-only Result and literal-only macros; map Pubkey parsing errors to the fixed code. Its existing ensure messages remain literal. Callback assert payloads are never formatted by the installed panic hook; callback order and attempt selection are unchanged.
- `diagnostics.rs`: Error stores only `&'static str`, no source error or backtrace. `err<T>` accepts no formatting trait and stores no T. The helper macros accept only literal message syntax. Debug/Display can expose only the stored static message. Main emits a single constant for every returned error. The panic hook ignores PanicHookInfo and writes exactly `client panic\n`, ignoring an I/O failure; no default hook, payload, location or backtrace formatting is invoked.
- The `client` profile inherits all optimized release settings and sets panic=abort. `build-client.sh` selects only devnet_spend, exact deployed feature flags and Rust 1.94.1 via the existing directory toolchain pin. A compile guard rejects a non-test client built without Linux/raw backend/abort. The root workspace release profile is untouched. The standalone profile can apply to another target only if someone explicitly builds that target with `--profile client`; the provided recipe selects just the client. Host dependency libraries, including program libraries, inherit abort in that native build; the three separate SBF builds do not.

## Backtrace mechanism and limits

Before reading stdin or creating any witness/worker/error, initialize installs the fixed hook, sets both RUST_BACKTRACE and RUST_LIB_BACKTRACE to `0`, and calls std::backtrace::Backtrace::capture once. In pinned Rust 1.94.1, `enabled()` stores the disabled answer as 1 in its process-wide AtomicU8; future capture calls return before reading the environment. Anyhow 1.0.104 calls precisely this std capture function. Its own constructor cannot override the cached disabled answer. Later environment changes cannot re-enable it. An unexpectedly pre-enabled cache fails closed by aborting before input processing. The custom client Error never constructs anyhow at all; dependency errors still use the primed std mechanism.

This is process initialization plus a pinned std implementation argument, not removal of the Backtrace API from libstd. `Backtrace::force_capture` bypasses the cache and must remain absent from the reached cone. No project crate/program/client helper calls it; source evidence and dependency snapshots are retained. This draft does not claim to disable arbitrary injected machine code, debugger capture or OS core/crash collection. The hook controls Rust panic diagnostic requests; OS abort status and external reporting remain observer/OS obligations. No environment-only backtrace re-enable path remains in the selected std/anyhow capture route.

## Entropy selection

The build recipe supplies `--cfg getrandom_backend="linux_raw"` globally to this host Cargo invocation, with explicit check-cfg and bounded linker flags. It unsets CARGO_ENCODED_RUSTFLAGS so that variable cannot silently supersede the selected flags. getrandom 0.3.4 backends.rs chooses linux_raw before target defaults. On x86_64 it issues inline-assembly `syscall` number 318; it neither resolves nor calls libc getrandom, and has no file fallback. Kernel versions without that syscall, or policy denials, now return errors instead of selecting the historical fallback; these are intentional compatibility differences, mapped to the fixed client error. The backend keeps its partial-progress/EINTR handling. This changes the selected source body: historical V225 dispatch/fallback proofs do not automatically bind it. E1/E2, native syscall/error/control association and the existing T fields remain obligations; no trust field is added.

## Optional stdout change

`OPTIONAL-remove-timing.diff` separately removes prove_wall_seconds and its now-unused clock reads/import. It is NOT applied, compiled or included in the measured client hash. The main patch retains stdout JSON, including the success-guarded mask_audit Debug string and public attempt count. Removing the field does not remove external timing observations or repair the Result-only headline interface; D478 remains unchanged either way.

## Allocation-failure diagnostic repair

The client-local global allocator delegates alloc/alloc_zeroed/realloc/dealloc to std::alloc::System. On a null allocation result it aborts immediately, before std's default allocation-error handler can print a dynamic requested size. Successful allocations and deallocation retain the same System calls and layouts. There is one null check per allocating call; no allocation-failure logging or new formatter. This is included in the measured diff and binary. Capacity-overflow panics still take the fixed hook. The allocator is defined only in the client module, so neither root-workspace program nor harness-library allocation is changed. The allocation failure event, addresses and external OS/crash observations stay under rdea-1/V400 and D159; this source change does not prove them public.

The first actual-client runtime gate (69212) passed on the pre-allocator draft. It is retained as intermediate evidence and superseded by the final-client runtime gate. The three ELF rebuilds remain applicable: the added allocator is in the tool client alone, outside every on-chain compilation input.

## Validation results

- Final client source freeze: `d42f8a4db548bccd06e15bcd64c9fd98abe423a9`; Rust 1.94.1 / e408947bfd200af42db322daf0fadfe7e26d3bd1 / LLVM 21.1.8; x86_64-unknown-linux-gnu; client profile, exact deployed feature flags, locked/offline build. SHA-256 **05673e4da06b3dbcf9890eb3737011375ce2a5a0f1a7f58e36179910f630a833**, 2,329,688 bytes. The earlier pre-allocator binary was 75b6ac55… and is superseded, not the delivered draft artifact.
- Optimized existing unit tests: all 3 account-policy/route tests pass, including first/rejected/last selection, invalid ABI and no generic fallback. Final source rerun is included in 69214.
- Optimized existing `RealR1_client::tests`: all 4 pass (transfer, withdrawal and both direct-baseline controls). These exercise proof construction and strict verification and retain durable nonce ledgers. Their ordinary noisy durations are not performance evidence. Accepted focused run: 69211.
- Existing actual-client gate: final run in 69214 passes all 4 combinations of transfer/withdrawal and default/devnet verifier, with the rebuilt Pool ELF. It checks selected attempt keys, stage1, stage2, settlement, duplicate-key failure/unchanged ledger and no fallback. `runtime-private-final/acceptance.json` contains public receipts only; host private key/recovery files are retained and excluded from export.
- Final controls in 69214: invalid JSON exits 1 with exactly `client error\n`; malformed input panic exits SIGABRT with exactly `client panic\n`. Controlled allocation failure exits SIGABRT with zero stdout/stderr. The helper links the final client's exact getrandom/anyhow rlibs and production diagnostics module. With inherited backtrace variables enabled and then changed back to enabled after initialization, std and anyhow statuses both stay Disabled. The direct backend succeeds under the getrandom interposer with zero intercepted calls; the matched old-backend control performs one successful zero-length probe and one EIO-returning intercepted draw. The control uses the same getrandom 0.3.4 fallback source with its std feature, and is not falsely described as the full original binary. These are finite validation, supported by the pinned source mechanism, not universal privacy proofs.
- Every selected client-profile project/dependency source named by fresh dep-info was scanned for force_capture. The only candidate is proc-macro2's `wrapper.rs:53`, inside `#[cfg(procmacro2_backtrace)]`; this cfg is NOT enabled (recorded build-script output and fixed RUSTFLAGS), and the proc-macro compilation is build-time. There is no active force-capture call in this selected source set. libstd still defines the API; it is not called on the selected route.

The three rebuilt ELF identities (source commands and comparisons retained):

| Mode | SHA-256 | Bytes | Exit |
|---|---|---:|---:|
| default | f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4 | 1,563,728 | 0 |
| devnet | 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299 | 1,563,728 | 0 |
| Pool | 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548 | 605,704 | 0 |

All are byte-identical. SBF compiler output includes existing stack-size/overwritten-frame diagnostics despite exit 0; those logs are retained. Hash identity does not certify absence of historical stack/runtime issues. No verifier change, release-pin change or repin is made. The client-only profile and allocator do not enter those builds. The backend choice intentionally limits this new client recipe to Linux and changes old-kernel/denied-syscall fallback behavior; that compatibility cost is part of the proposal.

Four setup failures are retained without credit: 69205 named the interposer output without the linker's lib prefix; 69206 refused ambiguous cached getrandom rlibs; 69209 passed the three client tests but its unfocused root cargo test tried an unrelated integration test whose baseline helper was not exported; 69210 rejected incorrectly escaped check-cfg syntax before compilation. Replacements changed the library filename, explicit fingerprint/feature selection, focused `--lib` target and flag quoting respectively. 69208 and final 69214 pass the controls; 69211 passes the four fixtures. No failed command was rerun unchanged, no resource cap was raised, and no failure is treated as a source-law counterexample.

The original source-audit snapshot names collided for std and anyhow backtrace.rs. Both source hashes were correct in the receipt. `snapshot-correction.json` and separate hash-verified read-only exports repair the missing artifacts without changing or rebuilding a dependency.

## Quiet-window cost measurement

Scope 69215 runs the **actual baseline and final draft devnet_spend binaries**, not an instrumented prover surrogate. The baseline was rebuilt from a9a9781f8a's unchanged tool sources with the pinned toolchain, deployed features and original release recipe; it shares the unchanged crate sources and locked dependencies. Ten alternating pairs each contain both transfer and withdrawal calls to both binaries. Public fixture requests come from the actual-client gate; fresh public nonce labels are identical within each paired experiment, with isolated, retained fixture ledgers. All calls succeed on the first attempt. No key/account exists for the synthetic timing nonce labels.

The exclusive marker was created before admission, never extended, edited or deleted, and expires automatically after 900 seconds. Every before/after boundary guard observes no other populated capped user job; all calls finish before expiry. Timing scope: exit 0, wall 9:42.55, GNU peak RSS 604,136 KiB, swaps 0. `window-start.json`, `timing/binary-pins.json`, guards, thermal counters and full per-call samples are retained. Marker expiry is not used as approval or as evidence of an unthrottled run.

| Fixture | Baseline median seconds | Draft median seconds | Observed delta | +10% on these samples |
|---|---:|---:|---:|---|
| Transfer | 14.541803503 | 14.394631272 | -1.0121% | Within |
| Withdrawal | 14.314668174 | 14.215088057 | -0.6957% | Within |

**All 10 pairs are thermally throttled. Zero unthrottled pairs were obtained.** The observed quiet-host medians are below the +10% budget, but the preselected minimum of five unthrottled pairs is unmet: the unthrottled performance gate is **UNDECIDED**, not PASS. These small negative deltas are descriptive fixture measurements, not a proven speedup, universal cost bound or timing/privacy theorem. External elapsed time remains observable under D478, with or without the optional JSON-field removal.

## Premise and adoption accounting

Endpoint premises removed/added/weakened/changed: **0/0/0/0**. No Lean or Kani is run. This is a source proposal plus finite validation and cost evidence, not a DIAG acquisition proof, native syscall refinement, universal failure-independence law or release/privacy theorem.

Before → proposed draft: arbitrary Debug/error-source/backtrace storage at the client boundary → literal-only storage and no operand formatting; environment-selected std/anyhow capture → disabled, primed capture route; default panic payload/location/unwind reporting → fixed hook plus abort; System null → std's size-bearing allocation error becomes System null → silent abort; getrandom dynamic dispatch/file fallback → inline raw syscall/error. These changes simplify future DIAG and V225 bindings; they do not install those bindings or discharge V400's joint public-failure/occurrence law. Dynamic event occurrence, ordered prefixes, files/recovery data, stdout acquisition, delivery/partial writes, allocator/world effects, crash/raw-memory reporting, E1/E2, L1/L2/L3, V370 and D381/D386 remain at their existing boundaries. T is still exactly entropy_law, entropy_kernel and observation. No new bad event, observer narrowing or trust field is introduced.

The delivered code is **experimental and NOT ADOPTED**. No merge, push, candidate/research write or repin occurred. The next owner deliverable is review of PATCH.diff plus this measured cost packet and a decision whether to adopt D474(C); any adoption still needs the corresponding source/observation associations and client release decision. D478 remains separate.

## Differential configuration and fixed-coin preflight

The initial historical root-workspace probe recipe enables optimized-terminal; the deployed standalone client does not. Workspace metadata alone is a feature superset and is not evidence of a particular target's selected features. Exact `--unit-graph` queries (graph-only under RUSTC_BOOTSTRAP=1, never code generation) record the actual targets, dependency features and profiles. Production builds unset bootstrap.

To avoid testing the candidate under the historical probe configuration, the final differential and fixture harnesses register the **unchanged existing example source files** as two validation-only targets in a copy of the client's standalone manifest/lockfile. Dependencies still point to the same pinned crate sources and reuse the final client's compiled cache. No crate source or production manifest is changed for this. `validation-Cargo.toml` records target registration and removal of the irrelevant default-run. The final harnesses select r1p-check plus aspis-r1-cost-probe/ct-host-prover, the client/abort profile, and linux_raw, exactly like the draft client. `client-harness-parity.json` mechanically compares every shared dependency unit's features and profile against the actual client: **zero mismatches**. The unchanged public-work-trace cfg is disabled on both sides of the existing corpus harness; its public_work field is empty, so this run does not newly establish an instrumented worker-event law.

The historical fixed-coin gate passed at 69216. The same fixture source was then rebuilt in the exact client configuration (69217) and its separate fixed-coin gate passes at 69218. Both compare complete proof/public bytes, canonical result records excluding elapsed seconds, and physical durable ledger bytes against the hash-verified retained golden fixtures. No unchanged control proof generation is repeated. The 1,000-pair run uses only the new exact-client-configuration candidate harness, against the existing gate's pinned c57a344726 reference executable. This is finite differential validation of the full retry owner, separate from the actual operational planner tests and actual-client timing above.

## Process notes

All native launches require exit 0 and allowed:true at admission and at the in-scope barrier, with MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0 and TasksMax=64. At most one capped scope runs for this job. The long differential uses three prover processes within that one scope and explicitly checks task-limit and OOM counters, with a resource review every ten minutes; its heavy step is optimized P_R1 proof generation/elimination, not compilation or kernel reduction. No Lean/env-J or Kani submission is made.

Early read-only monitoring/source reads used a separate SSH connection while a short foreground scope's SSH connection was still open, contrary to the common no-extra-parallel-SSH transport rule. No ControlMaster, duplicate compiler submission or shared-source mutation resulted. The long differential instead detaches exactly once and polls through one short read-only SSH connection at a time. This process deviation is recorded rather than described as full transport compliance.

External process medians, which include startup, are also retained: transfer 14.554147054 → 14.406396608 seconds (-1.0152%); withdrawal 14.325851486 → 14.226371763 seconds (-0.6944%). These have the same throttling limitation.

The initial source upload also preceded the first reservation receipt, contrary to the common pre-SCP receipt instruction. All actual capped builds/tests/timing launches still had accepted pre-launch and in-scope admissions; the upload omission is not described as compliant preflight.

## Completed 1,000-pair differential and final binding

Scope **69219 passes 1,000/1,000**, coins 6000–6999, against the existing gate's c57a344726 reference (sha256 3c31fe5786de3197c66c4fae5a3897599a2c2e94b449780903fd18cb672a96c1). The exact-client-configuration candidate harness is 4501002d2d870e43d1d3252baad3d5e69afbb04b4645a48429e401bf6df6a582. There are 600 successful full proof pairs (including 100 forced rejected-prefix pairs), 400 error pairs, both variants in every tape class, and four complete supplied-oracle comparisons. Complete public/proof bytes and result records, callback/ledger-event order and reservation contents agree. The follow-on audit independently checks every physical ledger file against the records and compares both sides: **1,000/1,000 pass**. This is finite differential validation, not a universal source-binding or privacy proof.

GNU wall **3:44:03**, peak process RSS **624,068 KiB**, swaps **0**; arithmetic-pipeline elapsed 13,441.958 s. Cgroup peak memory **5,360,091,136 bytes**, peak tasks **54/64**, swap current/peak 0; task-limit, high/max memory, OOM and OOM-kill counters all zero. Scheduled resource-review records are retained. Source/recipe freeze and exact binary pins are in the receipts and corpus manifests. The long gate was submitted once, with no transport retry or duplicate execution.

Scope **69220** verifies **1,283 source files with zero mismatches**, including the final production source, original baseline tool source, unchanged harness source/helpers and validation-only manifest/lockfile. It also verifies the final client hash and performs **literal whole-file byte comparisons** of each rebuilt ELF against retained reference artifacts: all three equal. The final new client, baseline client, actual-client gate and exact-configuration fixture/differential executables are retained under `/home/dombarker/project-offloads/codex-pv-c474-20261029/artifacts/`; rebuilt ELFs remain under `elf-default/`, `elf-devnet/`, `elf-pool/`. No binary, ELF or archive is committed.

All **85 generated task key files** are retained mode 0600, with private fixture directories and recovery/nonce ledgers retained. No wallet/account key is deleted, burned or unlinked; no authority or real on-chain balance is operated on. No key cleanup or refund is attempted, so no refund destination/signature is applicable. Cache cleanup first checks for key candidates and would retain/secure a whole cache containing any; none are found in the four rebuildable caches, which are removed. Corpus records, physical ledgers, recovery data, source snapshots and evidence artifacts remain. `final-audit.json` records paths and modes without private key contents.

## Final scope receipts and stop

**21/40 capped native scopes used: 17 passed, four setup failures corrected as recorded above. 0 Lean, 0 Kani, 0 env-J submissions.** Native labels use only 69200–69220. No memory kill, timeout, admission refusal, void launch, cap increase or unchanged failed-command resubmission. Exact commands/targets, source-revision labels, wall/RSS/swap and N/A native axioms status are retained in every receipt and aggregated in `attempts.json`. The runtime/proof source freeze is d42f8a4db5; later evidence commits do not change production code.

The requested experimental source/measurement packet is complete; the budget is not described as exhausted. Source, fixture, byte-identity and differential checks pass. The unthrottled +10% performance decision remains **UNDECIDED** because all quiet-window pairs were throttled; no unchanged timing run was repeated to seek a pass. Adoption, client repin, native/model associations and D478 joint observation work remain owner/future work. No privacy premise is removed and the target is not established.

| Scope | Target/phase | Exit | Wall | Peak RSS KiB | Swap | Revision | Axioms |
|---|---|---:|---|---:|---:|---|---|
| native69200 | compilation | 0 | 1:17.96 | 641900 | 0 | 0046a7446d | N/A native |
| native69201 | optimized-SBF-compilation | 0 | 0:29.82 | 646116 | 0 | 0046a7446d | N/A native |
| native69202 | optimized-SBF-compilation | 0 | 0:02.26 | 204908 | 0 | 0046a7446d | N/A native |
| native69203 | optimized-SBF-compilation | 0 | 0:26.65 | 644248 | 0 | 0046a7446d | N/A native |
| native69204 | optimized-baseline-and-runtime-harness-compilation | 0 | 0:30.84 | 573132 | 0 | 0046a7446d | N/A native |
| native69205 | direct-entropy-backtrace-and-error-controls | 1 | 0:01.32 | 132452 | 0 | 0046a7446d | N/A native |
| native69206 | corrected-interposer-link-and-controls | 1 | 0:01.35 | 131724 | 0 | 0046a7446d | N/A native |
| native69207 | optimized-differential-and-fixture-probe-compilation | 0 | 0:29.18 | 569728 | 0 | 0046a7446d | N/A native |
| native69208 | fingerprint-selected-interposition-control | 0 | 0:01.42 | 134568 | 0 | 0046a7446d | N/A native |
| native69209 | optimized-existing-unit-and-fixture-tests | 101 | 2:13.54 | 651932 | 0 | 0046a7446d | N/A native |
| native69210 | focused-optimized-existing-client-fixtures | 101 | 0:00.04 | 39228 | 0 | 0046a7446d | N/A native |
| native69211 | focused-fixtures-corrected-flag-quoting | 0 | 0:56.62 | 708848 | 0 | 0046a7446d | N/A native |
| native69212 | actual-planner-and-three-ELF-runtime-fixtures | 0 | 0:58.12 | 592112 | 0 | 0046a7446d | N/A native |
| native69213 | allocator-hardened-client-compilation | 0 | 0:01.08 | 254736 | 0 | d42f8a4db5 | N/A native |
| native69214 | allocator-hardened-unit-controls-runtime-and-source-audit | 0 | 0:59.73 | 590428 | 0 | d42f8a4db5 | N/A native |
| native69215 | quiet-paired-actual-client-prover-timing | 0 | 9:42.55 | 604136 | 0 | d42f8a4db5 | N/A native |
| native69216 | exact-unit-graphs-and-existing-fixed-fixture-byte-gate | 0 | 0:27.60 | 665540 | 0 | d42f8a4db5 | N/A native |
| native69217 | exact-client-configuration-differential-harness-compilation | 0 | 0:00.93 | 191124 | 0 | d42f8a4db5 | N/A native |
| native69218 | deployed-configuration-fixed-fixture-byte-gate | 0 | 0:27.88 | 669268 | 0 | d42f8a4db5 | N/A native |
| native69219 | optimized-full-retry-owner-differential-1000-pairs-and-ledger-audit | 0 | 3:44:03 | 624068 | 0 | f6edfb043d | N/A native |
| native69220 | final-source-ELF-artifact-key-retention-and-cache-audit | 0 | 0:01.20 | 32816 | 0 | f6edfb043d | N/A native |

Commits before final evidence-only commit (`git log --oneline a9a9781f8a..HEAD`):

```text
f6edfb043d Record diagnostic draft validation and quiet client timings
d42f8a4db5 Suppress allocation-size diagnostics in the experimental client
0046a7446d Draft fixed client diagnostics and direct kernel entropy recipe
```

The final evidence-only commit adds these completed receipts/report; it changes no production source.
