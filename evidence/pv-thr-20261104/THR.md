# D622 — scoped threads: coverage, cost, and recommendation

Research only, 2026-11-04. Worktree `/Users/dominic/ZK/.worktrees/pv-thr`,
branch `codex/pv-thr-20261104`, research base
`c0cfa4c4375531b9c85c349dc9922e794bcd5408`.
The evhB checkpoint examined is **db0b2b3fa32** on
`codex/pv-evhB-20261103`; all evhB citations below refer to that revision,
not its moving branch tip. No Lean, native, Kani, extraction or host job ran.
No certificate or premise removal is claimed.

## 1. Existing coverage: no full scoped-thread contract

**No inspected accepted item already supplies the requested functional
contract for this caller.** Existing boundaries support a proof strategy;
they do not discharge its missing source association.

| Authority inspected | What it supplies | What it does not supply |
|---|---|---|
| pv-common rdea-2 / LOG D567; rdea-2' / D583 | Stateful thread creation, TLS, joins, panics and stack resource answers; retained exhaustion/abort branches; a resource-granting trace may witness non-emptiness. Resource and failure independence remain P/V400 obligations. | Exactly-once capture execution, correspondence of a particular handle to a worker/result, or source handle transport. rdea-2' concerns stack resources, not a thread correctness theorem. |
| `design/PRIVACY-LEDGER-20261026.md`, “Owner decisions 2026-10-27 (B)”; `design/PV-OWNER-PACKET-20261027.md`, opening and fifth-amendment paragraphs | T is exactly `entropy_law`, `entropy_kernel`, `observation`; no further field or missing native fact may be folded into T. | Permission to add scoped-thread correctness under another name. |
| `R1Z/PV_RunJoin_TrustItems` retained in `evidence/privacy-recount-20261026/recount3/snapshots/runjoin/docs/research/v8-r0-zk-20261009/lean/` | `observation` equates native and extracted observations, including worker outcomes and the complete D159 payload. | Construction of the missing extracted/source execution or proof of its caller composition. The owner expressly leaves those as P. Its broad wording is not a license to postulate the desired thread/Code correspondence. |
| pv-common k'' / D523, k''' / D542 | Kani-to-deployed std transfer: exact reached items, token parity or a structural argument for **each differing ordinary item**, including results, panics and UB checks; intrinsics remain V370. | Correctness of a newly written std model, execution of unsupported std threads, or a certificate for code Kani never checked. |
| LOG D188; `design/TRUST-INVENTORY-APPENDIX-DRAFT-20261027.md`; D188 fidelity decision and owner-packet narrowing | Pinned extraction trust for specifically associated extracted bodies; safe extracted Vec/Box interpretation; narrowed fidelity/provenance qualifications. Non-extracted wrappers and composition require proof. | Blanket Rust/std correctness. No pinned extraction of this scoped-thread interval was supplied. Dropped restoration findings prohibit assuming ownership fidelity. |
| `R1Z/ProverCommitTrustedStd24.lean`, `TrustedStd`; trust inventory / `design/TRUST-AUDIT-20261026.md` | Enumerated map/set, sort/dedup, and live-key TLS laws on a designated single-thread schedule; soundness TrustedStd also has specific Option/Result/slice-copy laws. | `thread::scope`, `Scope::spawn`, `ScopedJoinHandle::join`, concurrent scheduling or handle linearity. A single-thread TLS law is not the required thread contract. |
| Stream A `docs/research/100bit-spend-path-20261013/design/C3-BIN-20261021.md`, runtime rulings and 2026-11-04 (aa)/(ab) | Specific allocator, runtime admission, hash syscall, data-only `RuntimePersistence`, and newly named `RuntimeReturnData` scopes. | Host scoped threads. (ab) explicitly says ReturnData **adds** trust and the owner may reject it; it is precedent for disclosure, not authorization to extend privacy T. |

The contract itself needs careful qualification. Successful creation starts
one closure with its actual captures; an abort can prevent completion and
pending/divergent workers can prevent join/scope return. On normal scope
return all its spawned workers have completed. Scope waits before propagating
an unwind in unwind-capable executions; process abort does not promise cleanup.
Join returns that worker's result or its owned panic payload when it returns.
Safe borrowing is not a theorem of effect independence: `F: Fn + Sync` can
access synchronized interior mutability. Prove the actual captures' reachable
state/frame properties; do not assume all such functions commute.

## 2. Exact source frontier

At evhB db0b2b3fa32, read `BLOCKER-D619.md`, `HANDOFF.md`, `OWNER-D619.md`
and `segmented-cut-D619.json` under `evidence/pv-evhB-20261103/`.
The frozen caller is `docs/research/v8-r0-zk-20261009/c3/check/src/native_workers.rs`:
`ordered_families` calls `ordered_map_inner(..., true)`. Its scope branch
spawns k=1..15, stores handles in source order, runs k=0, consumes handles
in order, then merges chunks. Its `is_worker()` branch remains part of the domain.

`handles.push(scope.spawn(move || run(k)))` evaluates the mutable receiver
before spawn. Scope activation, that held loan, exact captures (`&run`, k),
all subsequent pushes/spawns, `run(0)`, Vec iteration/moves and joins are
real instructions. tls-2 does not certify or erase them. Scope construction
itself reaches TLS before the callback. No fabricated Scope/handle is allowed.

The retained deployed std file
`evidence/pv-evhB-20261103/inputs/std-1.94.1-D618/scoped.rs` shows:
scope builds ScopeData, calls its callback once via catch_unwind, waits on
the running-thread count, then returns/rethrows; spawn delegates to
`Builder::spawn_scoped(...).expect(...)`; join delegates to its inner join.
Those delegations expose further obligations: packet/result ownership,
spawn backend, atomics, parking, TLS and drops. Reading the wrapper alone
does not prove their semantics.

Spawn returns a handle directly; creation failure panics, hence aborts in
the adopted panic=abort client. Worker `run(k)` returns
`thread::Result<Vec<T>>`, so join's full domain is
`thread::Result<thread::Result<Vec<T>>>`, plus nonreturning outcomes. Retain
both owned `Box<dyn Any + Send + 'static>` Err payloads as required by D619;
do not remove them merely because a fresh worker unwind normally aborts in
this profile. Preserve effects before every failure.

## 3. Alternative costs

### (a) Source-bound Lean interval, stateful world, OWNER Vec

**Highest proof/association effort; zero additional trust if completed.**
Reuse `lean/PV_EVHB_SpawnCaller{,G}.lean`, `PV_EVHB_OWNER.lean` and the
growth/storage/source-lifetime laws. They already give constructor/receiver,
spawn-post-world and loop schema facts. They explicitly do **not** provide
the full native instance, element-drop/iterator coverage or closed thread ports.
Cost is not just one induction: extend to the complete interval, tracked
linear worker identities and captures, Vec realloc/moves/consumption/drop,
scope activation/completion, nested replies, all failure/pending prefixes,
and the original continuation/world/events. Close actual worker contracts.

Bind every source instruction of the deployed caller and reached std wrappers
to Code, statement by statement (own-1 / structural source binding). For
toolchain differences use k''/k''' exact per-item parity; **parity alone
cannot replace this binding**. Native hybrid certificates may cover the
executable straight segments with their reached controls, but may not claim
the unexecuted interval. A new hand-written interpreter alone proves only
its own model (LOG D610), unless this source association is supplied.

OS primitive answers remain stateful rdea-2 P obligations, with explicit
admissibility/ownership/result laws and witness-independent request/failure
timing. Arbitrary unrelated spawn/join replies cannot imply exactly-once
result provenance. Derive the std contract from the bound source and named
primitive laws; keep any unresolved backend law as P, never as an assumed
closed instance. Compiler/intrinsics remain V370; physical storage remains L3.
No reliable wall-time or attempt estimate follows from the inspected evidence.

### (b) Sequential kani::stub for scope/spawn/join

**Smaller model/harness effort, unchanged native adequacy debt.** A stub
needs a separate model carrier: it cannot legally manufacture the actual
opaque Scope or ScopedJoinHandle. Type/API compatibility is itself a blocker
under tls-1/tls-2, not solved by writing an eager callback.

A PASS would prove caller behavior relative to the stub. To transfer it,
one additionally needs **native scoped-thread behavior refines the sequential
model**: exactly-once captures, handle/result association, completion and
failure semantics, memory frames, and any serialized scheduling effects.
That is the missing std contract, not existing P6 tool trust. An eager
fixed-success stub additionally erases exhaustion, panic, pending, TLS,
allocation and observable scheduling/time behavior; it violates the rulings.
Even output serializability needs a proof for these actual workers; it does
not imply D159 trace/timing equality. A nondeterministic full-reply model
retains failures but still does not establish native handle transport.

If this refinement is proved, (b) is a conditional proof aid with no new T;
if accepted without proof, it is new scoped-thread/serialization trust,
requiring owner amendment just as (c). k''' cannot validate a semantic stub
by comparing the two versions of std. Future runs also require k3 local
records/reached failing controls and all applicable copy/feature safeguards.

### (c) New `RuntimeScopedThreads` row

**Least std proof work; explicit increase in privacy trust.** A proposed row
would specify successful spawn/capture ownership and worker identity,
one invocation, matching join result/payload, completion before scope return,
borrow/frame guarantees and the deployed panic/abort behavior. It must leave
resource denial, divergence, diagnostics and schedule/failure timing visible;
it cannot assert unconditional success or eventual completion.

Even with that row, the caller's Vec/handle transport and model composition
still need proof. The row would replace std/backend proof debt, not prove
`handles.push` or joins select the right handle. There is **no spare T slot**:
3 -> 4 independent trust items violates the owner's cap, even if encoded
inside `observation` or outside the record. Only the owner can explicitly
amend the cap/scope. Stream A's RuntimeReturnData addition does not override
the privacy decision. No such amendment is recorded or adopted here.

## 4. Recommendation and first theorem

**Recommend (a), with its source-binding requirement, not a model-only Lean
replacement for route (c).** This is authorized proof work within the present
trust contract; the owner need not decide mathematical proof steps. A lead
method review may be needed for the precise structural certificate format;
it cannot grant missing semantics. If completion instead requires accepting
an unproved std/backend contract, stop that closure claim and request the
owner decision described in (c), explicitly recommending whether to amend T.

First proposed theorem: **`ordered_families_spawn_prefix_linear`** (a
specification here, not a compiled Lean declaration). Starting from the
original source entry and scope activation, for each reached prefix with
successful spawns 1..j, derive that the same live handles Vec contains exactly
those j distinct worker tokens in that order, each linked to its recorded
(`&run`, k) capture and still-live activation. Show the next source receiver
loan and spawn/push preserve the invariant across growth and moves; an abort
or pending reply retains the exact prefix, world and continuation. Do not
assume an initialized owner, desired Config, or whole-helper equality.

Prove its local preservation step first using the existing constructor and
spawn-post-world laws, then source loop induction and the pinned structural
binding. Follow with handle-consuming iterator/join provenance, run(0), scope
completion and full interval-to-Code equality. The resulting claim is exact
source-level result/state/ownership/effect correspondence for all admitted
actual callers and legal stateful histories, not guaranteed successful threads
or schedule-independent physical timing. Worker independence, native event
encoding, V400, allocator adequacy and V370/L3 stay named until discharged.

Before/after this research: D619's native interval association **OPEN -> OPEN**;
privacy premises removed/added/changed **0/0/0**; T **3 -> 3**. No alternative
is implemented or certified. Validation is read-only source/statement review
and git whitespace/path checks only; formal target, wall/RSS/swap and axioms
receipts are not applicable because no formal job ran. Target not yet established.
