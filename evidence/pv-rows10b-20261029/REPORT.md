# PV_ROWS10B resume D486 — conditional decompositions and source-binding blockers

**V225 and V403 remain SUSPENDED. No row is restored or closed, no privacy or
deployment premise is removed, and the privacy target is not established.
T is unchanged.** This report distinguishes conditional model results from
native association; neither model witnesses nor controlled-loader/cache tests
are honest-run deployed privacy counterexamples.

Worktree: exactly `/Users/dominic/ZK/.worktrees/pv-rows10`, sparse checkout.
Branch: `codex/pv-rows10b-20261029`, inherited candidate `05fdae5a3b`.
New modules: `PV_ROWS10B_*`. Host workspace:
`/home/dombarker/project-offloads/codex-pv-rows10b-20261029/`.
Receipts: this directory; branch commits before the final reporting commit: `COMMITS.txt`.

## V225 — SUSPENDED at one exact first blocking link

**Blocker:** establish `PV_ROWS10B_Link_SymbolOrigin` for the actual admitted
runtime's `dlsym(RTLD_DEFAULT,"getrandom")` result and every callable value read
from `GETRANDOM_FN`: the selected pointer must be the intended implementation
whose source is bound to the stated syscall interface. No actual deployment
loader/library/cache provenance certificate is supplied by the retained source
and feature pins. A successful zero-length probe does not establish it.

This is the first blocked source-binding link, not a claim that all downstream
own-1 links have been discharged. It prevents an unconditional binding of this
backend to `getrandom(2)`. It is a P obligation; it must not be added to T or
silently delegated to V370. V370 retains the existing source-to-machine-code
compiler preservation obligation; it does not select a dynamic symbol.

Before: install the actual selected op129, including its complete returned
slice, inner OS error, outer failure/divergence, effects and entropy callback
association. After: that native installation remains open. The compiled new
results are conditional operation/control schemas, explicit model witnesses,
and dispatch/control helper laws. They do **not** establish full own-1 binding.

### Compiled consumed law and ruling-(v) witnesses

`PV_ROWS10B_Consumed.Op E` has the exact op129 type schema:
`Slice U8 → Aeneas.Std.Result ((core.result.Result Unit E) × Slice U8)`.
The dictionary's external Error remains a parameter; no replacement Error type
is installed. `consumed` composes the named Entry, Body, Control, Public and
Callback links. Entry selects the source operation; Body is the still-required
complete source-wrapper/backend association; Control supplies the control
interpretation; Public couples environmental words; Callback associates the
consumed density with the retained law. These are P links, not discharged by
the theorem. The complete Result equality is retained alongside publicness of
`Stop`, which distinguishes returned OS success/error, outer failure with its
error, and divergence. It does not discard the returned buffer on inner error.

Immediately after the consumed theorem compiled (68602), the conjunction's
explicit model witness was attempted (68603) and compiled after a proof fix
(68604). It uses two Bool witnesses sharing an environment and includes models
of inner error, outer panic, divergence and success at different request
lengths. It is not a native execution. `PV_ROWS10B_Exact64.consumed64` and
`exact_links_satisfiable` specialize the same construction to the exact Raw
carrier `Fin 2 → Fin 32 → UInt8`, with requests of length 64. Finite-cardinality
instances remain ordinary typeclass parameters, as in the consumed density
schema. `decode` defines the two contiguous 32-byte coordinates with a proved
index bound. Its association with the actual callback/native weight is not
installed here.

The successful-byte density premise has exactly E1's formula on exactly that
Raw carrier. Source checks mechanically verify the aliases and formula against
`ProverCommitPublicNonce40.E1`, `FsStatement.OracleAnswer`, and the unchanged
TrustItems fields. This is a specialization of the retained **schema**, not an
imported/instantiated TrustItems deployment certificate. No native successful-
byte uniformity was proved; the literal density in a model satisfiability
witness is only an explicit model density. `T.entropy_kernel` remains exactly
the native joint-weight equality with `PV_RunJoin_E1Joint.weight 128 ...`; no
syscall-fragment independence or product law replaces it. T.observation is also
unchanged. None of these fields establishes dynamic-symbol provenance or
actual boundary-control publicness.

### Selected backend, explicit control interface, and source evidence

`PV_ROWS10B_Dispatch` models null/sentinel/callable cache cases, the glibc dlsym
selection, and the deployed Linux probe decisions: negative ENOSYS/EPERM falls
back; EIO retains the pointer; a cached callable is not reprobed.
`selected_origin` consumes the new explicit SymbolOrigin link, with its own
present-symbol, successful-probe satisfiability witness.
`probe_not_symbol_binding` refutes the unconditional provenance shortcut.

`PV_ROWS10B_ControlWord` exposes pointer loads/stores, dlsym/probe, FD loads,
compare-exchange, futex wait/wake, `/dev/random` open/poll/close,
`/dev/urandom` open, getrandom and read as distinct control sites. It exposes
signed return counts, errno, request amount and flags. Control helpers include
partial counts, EINTR, unexpected returns, Error's negative OS encoding and
internal 65537/65538 encodings, FD publication/reset and poll-error close.
`PV_ROWS10B_Retry` proves a symbolic infinite EINTR word remains pending on
EVERY finite prefix; only then is model divergence claimed. It also proves
complete wrapper inner-error, outer-failure and divergence branches.

These are owned control/Result helper proofs. They are **not** a full
statement-by-statement structural (K-1 substitute) certificate for the selected
backend. `source-audit.json` explicitly marks `complete_own1_binding:false` and
records 20 checked source coordinates and 8 candidate source pins. Actual
pointer/FD atomic World effects, libc/dynamic-target-to-syscall refinement,
mutable-memory/restoration, actual complete control-word publicness and native
callback coordinates remain downstream P work. They are not projected away or
assumed true. The 64-byte caller source is pinned: public-nonce guard, sixteen-
candidate limit, fresh zeroed 64-byte destination, `fill(...)?`, then the two
32-byte copies and zero guards. Fixed length proves no environmental control
coupling by itself. `PV_ROWS10B_Link_ActualControlPublic` remains uninstantiated
on that caller.

Two optimized capped native scopes provide **finite validation**:

- `native-01`, `dispatch-native-result.json`: the original getrandom 0.3.4
  deployed-configuration rlib executes two ordinary successful 64-byte calls.
  The same executable under a controlled LD_PRELOAD library observes exactly
  one successful zero-byte probe and two cached calls to the interposed
  function, each returning EIO and leaving written bytes. The interposed
  function performs no entropy syscall. The crate body, features, profile and
  executable are unchanged across those runs. The runtime environment is
  deliberately controlled; this does not establish that such a loader state
  is admitted in the deployed privacy experiment, or that two honest witnesses
  produce these different signals. It is not a V225 privacy FINDING.
- `native-02`, `fallback-native-result.json`: unchanged source bodies with
  appended test-only accessors exercise empty-input skip, cold 64-byte fill,
  eight concurrent file-fallback calls, cached FD reuse, and controlled stale-
  FD EBADF. Every original file remains a byte-identical prefix; hashes and
  appended lengths are recorded. No `getrandom_test_*` cfg is enabled. This
  validates selected branches, not all schedules, infinite executions or
  universal source correspondence. Original sys_fill_exact's prior controlled
  partial-write/EINTR/error tests are reused read-only from the rows10 report.

Both receipts retain Rust 1.94.1, release optimization, disabled debug/overflow
checks, dependency hashes, exact commands, binary hashes and resolved features.
The full deployed crate feature/profile graph is in dispatch-native-result;
the fallback receipt references the same hash-checked graph. No ELF pin changes
are required because no release source was edited.

## V403 — SUSPENDED at actual caller-prefix instantiation

**Exact blocker:** instantiate `PV_ROWS10B_Link_CallerPrefix` for every actual
honest native op121 reached event, with the current selected dictionary and
the exact interpolation/semantic/update/read equations and round bound.
The native host caller now imports `aspis_prover::host_arithmetic`, whereas
op121's emitted selected name is the core sumcheck polynomial evaluator. No
native event association is obtained merely by matching those names.

Before and after: all 112 coefficient limbs and four challenge limbs at every
actual honest reached op121 call must be below 2147483647. No native event was
instantiated and no honest noncanonical event was found. No row premise is
removed, and the historical unrestricted noncanonical challenge is not claimed
reachable.

`PV_ROWS10B_CanonConsumed.consumed` decomposes the domain into named CallerPrefix,
PrefixEquations, RoundRange, Interpolation and Semantic links. The event stores
computational data/equations, not a canonicality field. Prefix/range obligations
apply to **occurring** events, not arbitrary unconstrained event structures.
`update_read` is discharged directly from the pinned Aeneas array specifications.
The four-U32 limb interface and 28/10 array sizes match the intended specialization;
the actual QM31/native dictionary specialization is not installed by this generic
schema. Existing actual-carrier producer theorems remain as recorded in the prior
rows10 report; they were not rebuilt, imported under a different cohort, or
claimed to prove the native reach relation here.

Immediately after this theorem compiled (68612), `CanonSatisfiable` compiled
(68613). Its conjunction witness uses actual Aeneas fixed-array update/read,
explicit interpolation/semantic model operations and a nonempty reached event.
It proves all five links together plus a reached event, without using an empty
reach relation. This is an explicit model instance, not an actual fixture run.
It satisfies ruling (v) for this generic schema and supplies no native closure.

V249, V263, V404 and V405 were not advanced in this focused resume; their prior
SUSPENDED statements and evidence remain exactly as in the rows10 report.

## Combined result, receipts and reproducibility

`PV_ROWS10B_Combined.local_results` combines only the two explicit model
non-vacuity certificates, the dispatch shortcut counterexample and genuine
model infinite retry. Its `ModelPackage` is printed in the audit so no native
or endpoint assertion is hidden in its fields. The audit prints every new
pre-replay theorem's axioms and the complete consumed statement schemas.
The replay distinguishes outer failure/divergence from the returned OS-error
signal, and checks the frozen focused import closure once. This is the new
model cone, not a replay or proof of the deployed privacy endpoint.

AGENTS.md section 6 evidence is in `attempt-summary.json` and
`attempt-summary.md`: exact target/command, exit, wall time, peak RSS, swap,
source revision and full `#print axioms` output location for every launch.
Every submission records the committed source path, git blob and sha256.
Native axioms are N/A. Final audit/replay outputs contain standard axioms only:
subsets of propext, Classical.choice and Quot.sound. Failed elaborations'
automatic sorryAx diagnostics have no proof credit; the accepted sources have
no hand-written sorry/admit/axiom/native_decide/implemented_by or XR imports.

All scopes use MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64;
Lean uses -M7000, one module/scope at a time. No memory kill, timeout,
reservation refusal, void admission, or transport interruption occurred.
Source fixes precede every failed-proof replacement; no failed source was
rerun unchanged. Ruling-(u)'s guard hash is in `validation.json`. All IDs were
scanned against other job receipts and shared sent files before use. Only
68600–68614 and audit IDs 68697–68699 are used.

The inherited rows10 environment is reused byte-for-byte, with its toolchain
and LEAN_PATH prefix. All 5,673 external objects were hash-checked before the
first compile. Only new PV_ROWS10B project objects are imported; those objects
are verified/reused between dependent targets (`own-object-verification.json`).
No project/external dependency was rebuilt merely to establish a new root;
no shared source/object was replaced. Historical rows10 source/native evidence
is reused read-only. Two initial identical preflight verifications overlapped
as read-only hash scans, before any compiler was launched; this was redundant
verification, not an unchanged failed compile or full regression. A sparse
`git add` refusal was fixed by adding only the new evidence/tools paths to the
sparse definition, before the first compile.

No crates/programs, existing proof, dictionary, simulator, observer, T, protected
soundness file, other worktree or shared launcher was edited. No keys were
created, used, read or removed. No binary/olean/ELF or file over 20 MB is committed.

The fresh budget is not exhausted. This resume stops at the explicit
source-binding suspension and the native caller-prefix suspension allowed by
the current instruction; it does not describe unused attempts as exhaustion
or model/finite validation as premise removal. Next concrete deliverable:
produce the admitted runtime's symbol/cache provenance certificate and bind
that selected dynamic callee to the stated syscall interface; then discharge
its complete effect/control interpretation at the actual 64-byte caller.

## Final usage and audit receipts

Fresh usage: **18/100 Lean attempts (11 passed, 7 failed), 2/30 native scopes (both passed), 0 Kani**. Budget remains unused; the stated native-association suspensions are the stop condition. No row premise was removed.

| Target | ID | Exit | Wall | Peak RSS KiB | Swap | Source revision | Axioms |
|---|---:|---:|---|---:|---:|---|---|
| R1Z/PV_ROWS10B_Combined | 68697 | 0 | 0:01.08 | 2633288 | 0 | 8bcdbce2523bb68850d28f840f06668cb9566e27 | standard only; lean-68697/output.log |
| R1Z/PV_ROWS10B_Audit | 68698 | 0 | 0:01.22 | 2626156 | 0 | d8f9cf671981b776edfe2b72321e264bfbefc8ab | standard only; lean-68698/output.log |
| R1Z/PV_ROWS10B_Replay | 68699 | 0 | 0:01.07 | 2630376 | 0 | ed85e41d89324de0e4604ed2f6ea17e3dcdef8e6 | standard only; lean-68699/output.log |
