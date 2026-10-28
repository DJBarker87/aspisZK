# World interpretation result — D364 resume

**Target not yet established. No row closed; no endpoint premise removed.**
This resume is in progress. W-CARRIER-1 is a finding about a design that
forgets destructor-accessible state, not a ledger/endpoint counterexample and
not a stop. The earlier report's stop disposition is superseded.

Exact worktree `/Users/dominic/ZK/.worktrees/pv-world`, unchanged branch
`codex/pv-world-20261028`; resume start `937b8f561de14683239b9f5f7abe74c7eafd013c`.
Original prover base `10b8afe7647d478f70693d8fc12e07be871c91e0`.
Host directory `/home/dombarker/project-offloads/codex-pv-world-20261028/`.
Budget at resume entry: 96 Lean attempts, zero Kani. All IDs stay in
36000–36199, excluding original uses 36000–36002 and 36197; 36198–36199 are
reserved final audits. `REFUSALS.md` records uncharged admission cooldowns.

## Established focused results

`PV_W_Enriched` retains process statics/atomics, live heap allocations and
ownership, allocator state, thread-local cells, volatile writes, ordering and
fences, unwind state and runtime-specific Extra. Its flag/counter witness
represents both retained normal/panic outcomes, counts one destructor entry,
and records an internal event. `drop_valid` and `project_threaded` establish
full-world continuity and OS projection through proven-silent steps. This is
not a proved representation of the shipped machine or all reached destructors.

`PV_W_Syntax` proves the typed state/error/trace interpreter agrees with an
independently defined operational execution judgment, including early-error
and divergence prefixes. `PV_W_SourceSyntax` supplies complete-Result erasure
and named bind/branch laws. These are model/source laws, not native purity.

`PV_W_Reservation` reifies the exact frozen directory-sync, fallible-reserve
and public store-reserve bodies. All three complete-Result erasure theorems
compile. The checked generator retains all 34 source call sites, arguments,
continuations and error branches. The finite source-tree proof generator
replaced unsuccessful congruence searches; caps were never raised.
`PV_W_ReservationThreading` composes those concrete source terms with ordered
operational world threading and enriched-state projection.

`PV_W_TypedEffects` and `PV_W_TypedReservation` retain typed open/sync/options/
error-kind/write arguments, with dictionary families for emitted generic
path conversions. Their erasure remains exactly the frozen Result.
`PV_W_TypedThreading` proves caller composition from local model-step laws;
those laws remain explicit obligations. Helpers are not asserted natively pure.
`PV_W_ErrorSyntax` proves error embedding preserves complete state/trace
results, allowing interpreter tape faults to remain distinct from native IO
error values. Focused receipts include their axiom reports.

## Still required

The requested **entire extracted prover → existing trust Observation** theorem
is not established. Prover entry staging, existing-OsWorld step models and
projection composition are being checked. The main nested proof routine,
reservation_path and other helpers still need recursive interpretations;
primitive native adequacy, actual reached Drop/implicit close and ownership,
allocator/zeroize fidelity, and the complete filesystem/D159 observation
producer and deployment binding remain P obligations. No partial threading
lemma is counted as that complete theorem or a native dictionary installation.

The original FXM native witness is retained at its committed pins. No new
reached-destructor purity theorem is borrowed from unfinished/unavailable
fxmem2 work. The original fixed-callback/forgotten-state findings remain
findings; they do not stop this resume.

## OS findings and row accounting

W-OS-1: O_EXCL exclusive creation/namespace behavior remains an owner finding.
W-OS-2: file sync and parent-directory-entry crash durability are distinct
owner obligations; nonce non-reuse across recovery depends on the required
persistence/recovery laws. Neither is assumed, and neither is a new T field.
OS-FINDINGS.md gives the dependencies. Native IO failure witness independence
under the adopted public-failure option is still unproved here.

V170 effectful cases and V171/V172/V175/V176/V267/V268/V271/V221/V222 remain
OPEN at their ROWS7 scope (`row-scope.json`). Endpoint statement, carriers,
observer (including L1/L2/L3), simulator, failure event and T are unchanged.
T remains exactly entropy_law, entropy_kernel, observation. Premises
removed/added/weakened: **0/0/0**. No source refinement gap is hidden in T.

## Validation boundary

Lean runs use one capped scope at a time: MemoryHigh=6G, MemoryMax=8G,
MemorySwapMax=0, TasksMax=64, -M7000. Exact commands, source revision/blob/SHA,
dependency fingerprints, exit, wall, RSS, swap and axiom output are retained.
Only successful standard-axiom results receive credit; failed sorryAx output
is rejected. No Kani, Rust/SBF rebuild, key/account operation, merge or push.
No changes under crates/ or programs/, frozen extraction, shared source tree,
or soundness/deployment files. No XR imports or proof shortcuts.

All 5,673 h4 external objects were hash-verified before the first resumed
compile. Split-object companion selection and the public-import scan repair
are documented. CACHE-SCAN-CORRECTION.md supersedes the initial incomplete
OS cache preflight; the failed consumer passed after full revalidation.
No unchanged full regression or full frozen manifest replay was run: no
row-closing native/deployment instance has been obtained.

History: `git log --oneline 10b8afe7647d478f70693d8fc12e07be871c91e0..HEAD`.
The final budget/audit/cleanup accounting will be recorded when this resume
stops under the task rules.
