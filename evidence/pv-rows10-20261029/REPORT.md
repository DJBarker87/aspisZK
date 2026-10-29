# PV_ROWS10: partial row investigation, 2026-10-29

**No assigned row is restored or closed. No privacy/deployment premise is removed.
The deployed privacy target is not established. T is unchanged.**

Branch `codex/pv-rows10-20261029`; exact worktree
`/Users/dominic/ZK/.worktrees/pv-rows10`; base
`42760700cbae39587de93f520aed51618e13ef0a`. Host workspace:
`/home/dombarker/project-offloads/codex-pv-rows10-20261029/`.
`COMMITS.txt` records the branch commits before the final reporting commit.
This is a partial handoff with unused budget, not a completed row-removal campaign.
The controlled-boundary counterexamples below refute particular proposed wrapper
shortcuts; they are **not** counterexamples to honest-run deployed privacy.

## V225 / op129 — SUSPENDED, with checked local counterexamples

Before: install the exact `Slice U8 -> Result (Result Unit Error × Slice U8)`
operation, including failures/divergence and the required entropy callback law.
After: that complete native association remains OPEN. The new accepted theorems
are owned finite-prefix/control and memory-length laws only. No dictionary
entry was changed and no complete-Result source binding is claimed.

The deployed dependency is getrandom **0.3.4**. `deployed-dependency-check.json`
checks the registry archive against the root lock checksum; registry source
hashes are in `dependency-source-pins.json`. The retained deployed build unit has
feature `std`, release profile, no extra rustflags. Its x86-64 Linux default
selects `linux_android_with_fallback`, not `linux_raw` and not the unconditional
`linux_getrandom` override. Sources are retained under `getrandom-0.3.4/`.

Statement-by-statement source inspection identifies this cone:

1. `fill` casts the mutable byte slice to MaybeUninit, calls `fill_uninit` with
   error propagation, and returns unit. `fill_uninit` skips an empty destination;
   otherwise it calls `backends::fill_inner` and returns the same initialized
   slice on success. References/unit/Copy error values introduce no owned-buffer
   destruction inside these wrappers. The caller's Zeroizing cleanup is separate.
2. The Linux backend Acquire-loads `GETRANDOM_FN`; a null entry invokes `init`.
   The glibc path uses `dlsym(RTLD_DEFAULT,"getrandom")`; initialization probes a
   zero-length request. Missing symbols, ENOSYS and Linux EPERM select the
   sentinel; the pointer/sentinel is Release-stored. A usable pointer calls
   `sys_fill_exact`, with flags 0, on the remaining destination. Sanitizer
   branches remain explicit in the retained source; this is not a proof of
   their compiled cfg selection.
3. The fallback loads the FD cache, opens or waits on uninitialized/in-progress
   state, and calls `read`. Initialization uses compare_exchange_weak, publishes
   the FD or resets the sentinel after failure, and wakes waiters. Linux
   readiness opens `/dev/random`, polls with infinite timeout, retries EINTR,
   closes that descriptor even after a poll error, then opens `/dev/urandom`.
   Open retries EINTR; futex wait/wake and descriptor-cache effects are retained.
4. `sys_fill_exact` calls the boundary on the remaining mutable slice. Positive
   returns convert to usize and advance through checked `get_mut(len..)`. -1
   reads errno, retries EINTR and propagates other errors; zero/other negative
   returns become UNEXPECTED. Non-positive errno has its own internal error.
   Invalid positive counts also produce UNEXPECTED. Memory written by the
   boundary must survive **all** these branches, including errors and EINTR.

This is an inspected source-cone inventory with script-checked source witnesses,
**not** the own-1/structural-(K-1-substitute) binding certificate. The outstanding
binding includes pointer/FD atomic states, fallback and libc-to-syscall paths,
precise Error encoding, mutable slice restoration, all failure/abort paths and
infinite retry/wait executions. The owned model's `prefix` constructor means an
unfinished finite prefix; it does not assert divergence. Its integer error tag
is an abstraction for local signal laws, not the actual Error representation.

### Exact T comparison

`PV_RunJoin_TrustItems.entropy_law` is exactly
`ProverCommitPublicNonce40.E1 d.law`: for every context and **Raw = Fin 2 ->
OracleAnswer**, the successful 64-byte return has weight `1/card Raw`.
`entropy_kernel` is exactly the equality of native joint weight and
`PV_RunJoin_E1Joint.weight 128 d.law d.frame d.coordinates`, for every coin.
Neither was changed, re-proved for Linux, or replaced by per-syscall uniformity.
There is no newly accepted independence, fairness, initialization, libc or
failure law. V370 and the owner's D381/D386 compiler boundary are retained.

The deployed body adds deterministic backend selection, caches, initialization,
partial-write accumulation, EINTR retries, errno/error conversion and return
buffer mechanics beyond these two *distributional statements*. It does not
establish the two statements. A 64-byte API draw may use several syscalls; no
independence/product law for syscall fragments is inferred. The exact 64-byte
memory-to-Raw association also remains an explicit source obligation.

The option-B public Boolean failure signal is the intended consumed projection.
`consumed_signal` proves it independent of the witness **given** named
`sourceBinding`, `publicControl` and `publicLength` links. `failure_control`
discharges the control projection for the owned finite-prefix model, and
`public_control_suffices` permits arbitrary initial/partial buffer contents.
The native source binding and actual publicness of the OS control trace are
not supplied. The full returned slice, error, world and physical observation
must remain in their respective associations; this Boolean is auxiliary.

Native scopes 01/02 compile the original unedited dependency `util_libc.rs` and
`error.rs` on Rust 1.94.1 with deployed profile settings and record all resolved
crate features and binary/input hashes. They are **finite controlled-boundary
validation**, not universal correspondence or execution of the shipped client.
Nine cases cover empty input, success, EINTR, partial success followed by error,
zero, invalid negative/count, and a boundary error that writes memory. One
live 64-byte `getrandom::fill` also succeeded; no entropy-quality inference is
made from it. Two checks reject shortcuts:

- identical 64-byte requests can yield different failure signals under different
  injected boundary replies;
- returning an error need not restore the old buffer in the *source wrapper*:
  injected EIO after a 16-byte write preserves that write.

The second check caused the owned model to be corrected before its final audit.
Neither test shows those injected schedules arise from two honest native
witness executions. They must not be promoted to such a FINDING.

Exact blocker: a full own-1 source binding through the selected backend to its
syscall boundary, followed by proof of actual boundary control publicness. The
current successful-byte trust fields are retained exactly, with no new T item.

## V403 / op121 caller canonicality — SUSPENDED

Before and after: for every actual honest-run op121 call, its 112 coefficient
limbs and four challenge limbs must be below P=2147483647. No native reached-call
instance was proved here; no honest-run counterexample was found.

`PV_Canon_Deployment.reached_canonical` still requires
`P_NativePrefixBinding base ops reached`. That predicate requires each native
call's arguments to equal an `ExtractedPrefix` with the interpolation, semantic
challenge, array update and readback equations, plus round<10. The existing
`op121_arguments` proves canonicality **from** those equations. Its hypotheses
are not an execution witness. Exact prior definitions are retained in `prior/`.

The selected host caller's source has interpolation, transcript semantic update,
then polynomial evaluation of `point[round]`; its recursive round entry and
native dictionary/caller association were not discharged. The current native
host caller imports `aspis_prover::host_arithmetic`, whereas op121's emitted
name is `aspis_core.state_only_sumcheck.evaluate_state_only_polynomial`; the
existing source/selected-operation association cannot be replaced by name
matching. This observation is not a new counterexample to the selected law.
The historical noncanonical 2^31 challenge is not claimed reachable.

Exact blocker: instantiate the native prefix relation for every actual op121
caller and recursive entry, retaining the exact selected operation/feature
association. No canonicality premise was hidden in T.

## V249 / op232 p_r1_check — SUSPENDED

Before and after: the exact selected callback must return the complete
`Result (Bool × R1CheckTimes)`, including native failure/divergence and effects.
No implementation instance was installed.

The frozen `z4/z9e.rs::p_r1_check` initializes times, installs the quiet panic
hook, sets QUIET, enters catch_unwind, runs public_data / emit / conversion and
extracted_builders / check with four clock pairs and Option early exits, resets
QUIET and returns `matches!(verdict,Ok(Some(true)))` together with all times.
Hook installation is **outside** catch_unwind; a total callback model cannot
silently catch that prefix. QUIET_HOOK, panic hooks, thread-local QUIET and
Instant are actual influence channels, so own-2''' does not apply. They cannot
be erased because the verdict happens to depend on public challenges.

Exact blocker: full source/Result/effect association for the phase continuations,
primitive clock/timing representation, hook/TLS setup and panic/unwind/abort
branches, and the reached emit/build/check bodies. No timings, errors or
observable effects were projected away to obtain a closure.

## V263 / op257 host_work.map — SUSPENDED

Before and after: for arbitrary selected T/F/Fn instance and public stage/n,
install the complete native map callback law. This remains OPEN.

New **model arithmetic theorems** prove the frozen 16-way range formula's zero
start, adjacent endpoints, final endpoint=n, ordered bounds, and bounds for
every usize arithmetic intermediate when n is representable and k<16. These
are source arithmetic helpers, not a thread/source refinement.

Native scope04 includes the original frozen host_work/native_workers files,
checks their hashes and the deployed crate unit (`ct-host-prover`, without
`public-work-trace`), and runs an optimized source harness. It passes 65,616
range cases, including usize::MAX boundaries; ten map sizes with each index
called once and merged in order; a nested map; and two panicking ranges with
the first source-order panic resumed. This is **finite validation**. The
source harness uses 1.94.1/std directly and retains V370; it is not an execution
of the shipped binary. Scope03 failed in this job's package-ID selector before
compilation and was replaced by the corrected scope04, not rerun unchanged.

The source reads ACTIVE TLS to choose nested sequential execution, guards it
with Active's Drop, spawns scoped workers, catches each range's panic, joins
all handles and resumes the first source-order panic. Allocations and callback
outcomes remain physical. own-2''' is inapplicable both because map has inputs
and because of these influence channels; memory primitives and allocator
internals alone would not have disqualified it. rdea-1 remains the named
runtime/allocator adequacy boundary, not a new trust item.

Exact blocker: full callback/closure source association plus spawn/join,
TLS/Drop, panic/abort, allocation and ordered-result execution law. The partition
arithmetic and finite native passes do not supply it.

## V404 transfer; V405 withdrawal — both SUSPENDED

Before and after for **each** fixture: actual complete execution-reached entries,
ordering and any exclusions must be established on the admitted fixture route.
No per-fixture execution witness or new universal exclusion was produced.
The proven excluded set remains empty.

Read-only review of parked `ee0f9fb93c` resume10 is retained in `prior/`:
its four entropy/serialization/hash prefixes have not been jointly instantiated
on either native fixture. Its native association theorem inhabits reference
dictionaries; it does not prove the actual `compile_call`, public deployment,
external and record association tuple. words/publicCorr/admission/row_call,
ordered effects and whole proof/audit equations also remain. Conditional
op132/op231 and op84/noCatch prefixes, dictionary irrelevance/poisoning, static
imports and callback membership do not establish either fixture's actual
complete invocation set. No parked proof object was loaded or rebuilt.

Exact blockers: jointly instantiate the actual transfer tuple and, separately,
the actual withdrawal tuple; connect complete source control to the native
trace, covering success, early exit, error and divergence. No pending D474 or
D478 decision was assumed or used as the reason for suspension.

## Combined statement and verification scope

`PV_ROWS10_Combined.local_results` combines only the accepted owned entropy
control/memory-length and public range-arithmetic statements. It retains the
public control-word equality and length equality hypotheses. It is neither an
endpoint theorem nor a row-discharge certificate. `PV_ROWS10_Audit` prints every
new theorem's axioms; `PV_ROWS10_Replay` is the once-only frozen focused import
replay plus a tiny changed-error-buffer negative control.

Only new PV_ROWS10 modules were imported as project proof objects. The complete
5,673-object h4 external manifest was hash-checked before the first compile;
its inherited toolchain and LEAN_PATH were retained. No external object was
rebuilt or substituted. Current private sources and objects are checked by
`verify-own.py`, with hashes in `own-object-verification.json`; this job's own
compiled objects were reused. No other-job project cone needed rebuilding.
No new extraction was run, so x' std-source comparison and b3p6-1 token/extractor
reclassification are not claimed. No XR module was imported or copied.

## AGENTS.md section 6 receipts, failures and deviations

`attempt-summary.json` / `attempt-summary.md` contain every exact target, exit,
wall time, peak RSS, swap, source revision and axiom output reference. Complete
commands, source blobs/hashes and full outputs are in `683xx-submission.json`
and `lean-ID/{receipt.json,time.log,output.log}`; native equivalents also record
1.94.1, full unit feature/profile graphs and binary hashes. Native axioms are
N/A. Final accepted axioms are subsets of propext/Classical.choice/Quot.sound.
Failed elaborations' automatic sorryAx diagnostics have **no proof credit**;
no hand-written sorry/admit/axiom/native_decide/implemented_by occurs.

All compiler scopes use MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0,
TasksMax=64; Lean uses -M7000, one module and one scope at a time. No memory
kill, timeout, admission refusal or transport failure occurred. Lean failures
were import-name and local proof elaboration errors; each replacement changed
source. Ruling (u)'s unchanged-failed-source guard is in `lean.py`; its hash is
in `validation.json`. Admission is checked in the same remote command as launch
and again by the standing barrier. No void admission launch is credited.

Process deviations are recorded explicitly: the initial block scan finished
after attempt68300, rather than before it; it found no other-job collisions,
and subsequent launches scan first. An initial source-snapshot script referred
to an obsolete records path and was corrected to the actual statement-crate
builder. A private verification script initially substituted ROWS inside the
literal PV_ROWS10 string and failed before writing its result; its corrected
run verifies all private objects. The shell continued to compile68397 after
that failed private check; its source/object check was recovered immediately
afterward. This did not bypass scope admission, but is not represented as a
successful pre-audit check. Later audits use the successful verification.

Budget is **not exhausted**; see validation.json for exact usage. The work
stops as a partial handoff after the checked source-boundary counterexamples
and the listed unresolved native links. Those counterexamples invalidate local
shortcuts only. They do not justify claiming a full deployed row restoration
or a checked honest-run privacy violation. Further proof work is required.

No crates/programs, existing proofs, dictionary, simulator, observer, T,
protected soundness files, shared launcher or another worktree was edited.
No key was created, read, removed or used. No SBF rebuild was necessary because
release source was unchanged. No binaries or files over20MB are committed.
Private host proof artifacts remain available for verified dependent reuse.

Next concrete deliverable: finish V225's selected-backend own-1 binding with
an explicit syscall control-word interface, then prove that interface public
on the actual 64-byte entropy caller. Instantiate consumed_signal only after
both links are proved; do not infer the latter from successful-byte uniformity.
