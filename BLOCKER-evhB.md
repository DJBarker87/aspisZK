# D580 blocker: native reserve header delivery into the advancing world

## D582 partial construction; unchanged native target still OPEN

Five new modules now construct descriptor ownership, source-slot stores and
moves, pending allocation installation, source-shaped RawVec control, an
explicit world projection, and a returning allocator-side owner registry.
See `evidence/pv-evhB-20261103/OWNER-D582.md` for exact scope and receipts.
`PV_EVHB_OwnerRegistry.registered_header_delivery` proves the header equation
for its CONSTRUCTED returning model, with denial/overflow/no-growth included.
It is not the native `reached_reserve_header_delivery` statement below.

The unresolved step is now to initialize and select this registry from the
ORIGINAL native constructors/receiver places, retaining the same lifetime
identity through moves, and prove the full source-execution/returning-macro
projection for actual Global/System answers. The concrete `project` map and
`source_install_table` avoid assuming equality of world types or supplying
the desired header equality. They do not prove that the original native
receiver is the selected source slot. Numeric/layout interpretation, shrink
reachability/control, push's value/length stores, diagnostic/nonreturning
association and the v263 descriptor-view installation also remain open.

Source-phase finding: a successful realloc can invalidate ownership of the
OLD header before `set_ptr_and_cap`; the new `Pending` relation is installed
by its two stores. Drop consumes ownership without resetting the old header.
This is NOT a counterexample to reserve-return header delivery, and neither
requested final equation has been disproved. No native instance, new T field,
endpoint weakening, or allocator-adequacy discharge is claimed.

Final D582 accounting: IDs91222–91230 consumed (five accepted, four rejected);
next91231,65 attempts remain; audits91298–91299 unused. Axioms are summary-based.

## D580 generic Vec resume at c1b31fa688

The requested generic route was inspected against the pinned V183 interfaces,
the v263 D579 blocker and its reserve/push/ownership/world models, and the
deployed Rust 1.94.1 Vec/RawVec source snapshots. See `SHARED-VEC-D580.md` for
the full generic specification and exact v263 instance statement. Neither is
claimed proved or elaborated. The exact lemma and reached domain below are
unchanged.

The first missing construction is the native owner/call association in the
advancing world, preserved through RawVec's actual `self.ptr`/`self.cap`
assignments. V183 returns the old erased Vec; its metadata function receives no
owner token. V263 retains an Owner but its method hook receives only a site,
thread, length and layout. Neither inspected interface supplies that association.
The two RawVec source snapshots have identical SHA256, so this is not an
observed library-source version split. No reached-state counterexample was
found. A fresh arbitrary metadata/hook definition or a supplied adapter equality
would not prove the requested source-bound construction.

The generic theorem also needs complete native allocator/OS outcomes: V183's
total `Option Nat × S` step has no fault/divergence/exhaustion constructor.
Those branches need a stateful native interpreter and faithful returning
projection, not conversion to allocation denial. Stopped at this proof blocker
under the inherited focus rule, before further memory/world wrappers.

No Lean/native/Kani/extractor/host launch or new audit. No accepted proof source,
endpoint premise, deployment condition or T field changed. Accounting remains
next **91222**, **74 attempts**, audits **91298–91299 untouched**.
New read-only source receipt: `evidence/pv-evhB-20261103/shared-vec-D580.json`.

## Inherited exact obligation and evidence

Start: `b5854a3a17efc1ae5676046b1d8d4d69ddc4934c`, branch
`codex/pv-evhB-20261103`. Scope: native memory/resource fidelity and advancing
world threading only. Stopped on the missing lemma below, as instructed.
Target not established. No endpoint/deployment premise removed; T unchanged.

## Exact missing lemma

The first necessary law is **reached_reserve_header_delivery**. With the
existing namespaces opened, its conclusion is exactly this proposition:

```lean
-- Parameters: [ExternalTypes], S : Type,
-- runtime : R1Z.PV_RunJoin_AllocatorWorld63.Runtime S PV_EVH_Runtime.State,
-- w : R1Z.PV_FXM_ReserveWorld.World S PV_EVH_Runtime.State,
-- v : alloc.vec.Vec (Array Aeneas.Std.U8 32#usize), n : Aeneas.Std.Usize.
let e := R1Z.PV_RunJoin_AllocatorWorld63.execute runtime w v n
(runtime.metadata e.world v).address = e.buffer.address ∧
(runtime.metadata e.world v).capacity = e.buffer.capacity
```

Quantification: every call reached from the ORIGINAL extracted prover entry,
including the initial `derive_private_salts` reserve and subsequent reached
growth, at the actual deployed allocator/runtime instance. The precondition is
that `w` and `v` represent that reached native state and THAT owned vector,
with its admitted header/layout. The two equalities must be derived from the
deployed RawVec/Global/System operations and the physical header update; they
must not be supplied as a new compatibility field. On allocation error the
same law retains the old header and the NEW allocator post-state. Overflow
and no-growth paths retain their respective actual effects.

This is a requested proof statement, not an elaborated theorem or a new axiom.
The concrete deployed instance and its reached-state/owned-vector association
are themselves missing in the inspected interface. The statement does NOT
quantify over arbitrary, unconstrained Runtime instances.

## Why current accepted results do not prove it

At their pinned source revisions (see the existing
`evidence/pv-evhB-20261103/allocator-extension.json`):

- `R1Z.PV_RunJoin_AllocatorWorld63.Runtime` supplies arbitrary `step`, `shape`,
  `metadata` and `encode` functions. It has no metadata-update invariant or
  physical ownership/source association.
- `execute` returns `Execution.buffer` with the changed address/capacity.
  `PV_FXM_ReserveSelected.selected` instead returns `(returned ..., v)`:
  the extracted vector carries the element values, not that updated header.
- `PV_EVHB_ReserveWorld.reserve` returns that same `v` and `e.world`.
  Its `continuation` theorem correctly passes `e.world`; it cannot establish
  what `runtime.metadata e.world v` says at the next allocation.
- `PV_EVHB_SaltsReserve.selected_prefix` proves the original source prefix
  at a dictionary fixed to one world. `afterReserve` then calls the original
  loop under that dictionary. It does not reselect later effects at their
  post-worlds. `PV_EVHB_PrivateSaltsNew` still takes a whole-loop OPEN leaf.

The missing conclusion is not a consequence of Runtime's type: for an empty
vector, a metadata function constantly returning capacity zero satisfies its
sole `fits` field. With positive width, admitted request one and a successful
allocator answer, `finish` produces capacity one, while that metadata function
still returns zero. This is an interface-level symbolic obstruction, not a
native experiment, compiled counterexample, or counterexample to shipped code.

Simply forwarding the world through another caller wrapper would leave this
header delivery unproved. Defining metadata to read an arbitrary latest history
event would also leave the identity of the owned native vector unproved.

## Remaining native/resource obligations

Header delivery is necessary, not sufficient. The actual instance must also
bind width/alignment/padding and the request to the deployed source, prove
`PV_EVH_AllocatorWorld.ValidAnswer` for reached Global/System replies, and
associate V183 memory/live state with the SAME physical heap and vector owner.
Its `Option Nat` step always returns; it does not model nonreturning OS or
allocator outcomes. Such outcomes need actual stateful delivery with their
fault/divergence/exhaustion/abort and diagnostic prefixes retained.

`PV_EVH_NativeOperatorProver.entry_OPEN` remains a source-spine composition
with supplied leaves. `PV_EVHB_WorkerRequests` supplies potential public sizes,
not an advancing thread/TLS/spawn/join/scheduling/worker-panic interpreter for
op257. Neither those sizes nor header delivery establishes witness-independent
resource answers or failure occurrence/timing. Those remain rdea-1/rdea-2,
V400 runtime obligations; source-to-machine preservation stays V370. No new
T field is proposed.

Next concrete deliverable: construct and source-bind the reached owned-vector
runtime instance and prove `reached_reserve_header_delivery`; then carry that
instance's full world through each salt step, constructor/move and original
entry call, with stateful resource deliveries. Do not replace native adequacy
by a supplied whole-helper Result or assume the displayed equalities.

## Validation and accounting

Read-only inspection of the accepted bridge sources and the three pinned V183
source revisions; no accepted source edited or restaged. No Lean/Kani/native
run, host launch, new axiom audit, or unchanged regression. No new proof claim.
**74 attempts remain; next ID 91222; audit IDs 91298–91299 untouched.**
Existing receipt/axiom evidence is reused with its original summary-based
qualification; no raw coherence or release audit is claimed.

The inherited prompt chain also references `prompt-pv-evh4.txt`, absent at the
given scratchpad location (read returned ENOENT). The current task prompt,
handoff and available inherited rules were read; no missing-file contents are
invented. This is separate from the native proof blocker above.
