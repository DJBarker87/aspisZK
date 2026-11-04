# D580 shared native Vec correspondence — unresolved

## D582 construction update (original specifications below unchanged)

`PV_EVHB_RawVecOwner`, `PV_EVHB_RawVecSource`,
`PV_EVHB_RawVecProjection`, `PV_EVHB_OwnerRegistry` and
`PV_EVHB_RegistryStores` are accepted local
construction modules. The source-slot lookup and two header stores are
explicit; realloc uses a pending-allocation phase and drop consumes ownership.
The registry has a concrete source-world injection, source-place/store laws,
and a derived header-delivery equation for its returning model. It selects by
source-place identity, not element equality. See
`evidence/pv-evhB-20261103/OWNER-D582.md` and `owner-source-D582.json`.

This is NOT yet the generic source-bound native interpreter specified below.
Original constructor/receiver/lifetime association and the complete native
primitive/macro projection remain unproved; no constructed native v263
runtime/growth pair or descriptor-view instance is delivered. Both original
equations and binders below remain OPEN and unchanged. Source control models
retain complete outer outcomes, but their primitive/diagnostic bindings are
not native adequacy proofs. No reached counterexample is claimed. rdea-1,
rdea-2/V400, V370/L3 and V183 SUSPENDED(K-3) remain; no T/endpoint change.
Next91231;65 attempts remain; audits91298–91299 unused.

Resume source: `c1b31fa688727ff7e4a08216557f25eccb2a7a1e`, branch
`codex/pv-evhB-20261103`. V263 inspected at
`a5b8b16cf10ae7fa94a493a4e4723cefd83d3d1c`, including
`evidence/pv-v263-20261102/BLOCKER-D579.md` via `git show`.
No correspondence theorem or native instance was established in this resume.
The statements below are specifications, not accepted Lean declarations.

## Required generic theorem and domain

Construct ONE source-bound native Vec interpreter and its allocator-world
interpretation, for arbitrary element type `A`, from deployed Rust 1.94.1
`Vec::{try_reserve_exact,push,push_mut}`, `RawVec`/`RawVecInner`, `Global` and
`System`. Quantify over every owned vector, value, request and world reached
from the original extracted callers, with their actual layout and ownership
invariants. The interpretation must identify the same owner before and after
the call and through moves; it must not choose an owner by element equality.

The theorem must prove, jointly:

1. **Reserve:** on every returning branch, the original inner Rust Result and
   unchanged initialized element values agree with `AllocatorWorld63.execute`;
   the allocator post-state, memory/live interpretation and ordered allocation
   history agree; reading the SAME owned native header in that post-world gives
   `Execution.buffer.address` and `Execution.buffer.capacity`. Allocation denial
   preserves the old header and the allocator's NEW state; no-growth and
   overflow retain their respective effects. This header conclusion is derived
   from source assignments, never a field of a compatibility record.
2. **Push:** successful value erasure equals `GrowingPush.push` after successful
   ownership-metadata erasure, with the same post-world and event prefix.
   Reserved push makes no resource request; growth uses `grow_one`'s amortized
   capacity, not reserve-exact's capacity. Header installation precedes value
   storage, and storage precedes the length increment. Physical capacities are
   preserved on reserved pushes; retained buffer capacities are only lower
   bounds. Include zero-sized types and checked-add/layout overflow.
3. **Failures:** retain `.returned (.ok ...)`, `.returned (.fail ...)`,
   `.returned .div`, `.fault ...` and `.exhausted`, wherever their carriers
   admit them, with their exact post-worlds and ordered events. Include
   `handle_error`/`handle_alloc_error`, diagnostic and panic=abort prefixes.
   Allocator/OS nonreturn is not replaced by an `Option.none` return. The V183
   projection applies to returning allocator calls; it does not justify erasing
   nonreturning native branches from the generic interpreter.

Both instantiations must use this interpreter and proved source association.
Two independently chosen models with a new assumed equality would not meet
the requirement. The native same-memory interpretation and observation mapping
also need construction; equalities between the two existing World types are
not available merely because both carry a type parameter named `S`.

The generic push conclusion, using the existing v263 carriers with `open R1Z`,
is the following equation. Its binders are `S A : Type`, the CONSTRUCTED native
`runtime : PV_V263_RetainedMethods.Runtime S` and
`growth : PV_V263_RawGrowth.Runtime S`,
`layouts : PV_V263_RetainedMethods.Layouts`, `site thread : Nat`,
`owner : PV_V263_OwnedDrain.Owner A`, `value : A`, and
`w : PV_V263_World.State S`. The domain is all corresponding reached native
push calls, with `owner.allocation.layout = layouts.item` and native validity:

```lean
PV_V263_BufferLoop.mapAction
  (fun (o : PV_V263_OwnedDrain.Owner A) => o.initialized.values)
  (PV_V263_GrowingPush.push growth owner value) w =
PV_V263_BufferLoop.mapAction
  (fun (b : PV_V263_VectorDrain.Buffer A) => b.values)
  (PV_V263_RetainedMethods.push runtime layouts site thread
    owner.initialized value) w
```

For reserve, the generic conclusion is the exact header equation in
`BLOCKER-evhB.md` with the element type generalized to `A`, jointly with the
returning Result/world/history correspondence above. Instantiating `A` to
`Array Aeneas.Std.U8 32#usize` must recover the original binders and reached
domain unchanged. These are unproved specifications, not conditional adapter
theorems offered as discharge.

## Exact v263 instance for the lead

Keep D579's binders: `S B : Type`,
`runtime : R1Z.PV_V263_RetainedMethods.Runtime S`,
`growth : R1Z.PV_V263_RawGrowth.Runtime S`,
`layouts : R1Z.PV_V263_RetainedMethods.Layouts`,
`handles : R1Z.PV_V263_OwnedDrain.Owner A`, `task : A`,
`w : R1Z.PV_V263_World.State S`, where
`A := R1Z.PV_V263_RetainedSpine.Task S B`.

With `open R1Z`, the required conclusion is exactly:

```lean
PV_V263_BufferLoop.mapAction
  (fun (o : PV_V263_OwnedDrain.Owner A) => o.initialized.values)
  (PV_V263_GrowingPush.push growth handles task) w =
PV_V263_BufferLoop.mapAction
  (fun (b : PV_V263_VectorDrain.Buffer A) => b.values)
  (PV_V263_RetainedMethods.push runtime
    {layouts with item := layouts.handle} 2 0 handles.initialized task) w
```

Construct the native `runtime`/`growth` pair; prove this on ALL handle-owner,
task and world triples reached by the deployed spawn loop, with
`handles.allocation.layout = layouts.handle` and native allocation validity.
Do not quantify over unrelated arbitrary runtime/growth pairs. This equality
erases only successful ownership metadata: faults, Result, state and events
remain. No equality of buffer lower-bound and physical capacities is requested.
It is the displayed generic push equation instantiated with
`A := PV_V263_RetainedSpine.Task S B`, `site := 2`, `thread := 0`,
`owner := handles`, `value := task`, and `layouts := {layouts with item := layouts.handle}`.

## Source inspection and first missing construction

The two slices' RawVec source SHA256 is identical:
`0c006d1bedcc8c1aa6d8f37ad5553e1b14c452c732745612cf23c4663c090965`.
There is no RawVec source-version split in the inspected inputs.

Rust `raw_vec/mod.rs:754–773` computes checked capacity, calls `finish_grow`
with `?`, then calls `set_ptr_and_cap`; lines 741–747 assign `self.ptr` and
`self.cap`. `vec/mod.rs:1028–1042` tests fullness, calls `grow_one`, writes the
element and then increments length. These source stores identify what must
be interpreted; the source text alone does not construct its Lean interpreter.

`AllocatorWorld63.Runtime.metadata` takes only a world and an erased Vec.
`ReserveSelected.selected` returns that same Vec. Neither definition supplies
a source-derived owner lookup or updates its physical header. V263 has an
explicit `Owner`, but `MapSpine.VecCall.push` carries only site, thread, length
and layout; `RetainedMethods.push` invokes an unconstrained hook. Its hook
receives neither that Owner nor a pointer. A source-bound owner table/current
call association inside the advancing world could supply the information,
but none was found in the inspected interfaces. It remains to be constructed
from the reached source execution, rather than assumed.

In particular, value-only metadata must be single-valued: two owners represented
by equal erased Vecs at the SAME metadata lookup world cannot receive different
headers from that function. Whether source reachability/call selection prevents
such an ambiguity needs proof. No reached collision is established here; this
is not a counterexample to the requested reached-state lemma or shipped Rust.

The first missing deliverable is therefore the source-bound native owner/call
lookup and its preservation across the above assignments, allocator outcomes
and moves. V183's total `Option Nat × S` step additionally cannot by itself
supply the generic interpreter's fault/divergence/exhaustion branches. Installing
`GrowingPush.push` as the definition of the native hook would leave the source
association unproved. Choosing metadata from the last allocation event would
leave the same-owner association unproved.

## Status

evhB `reached_reserve_header_delivery`: OPEN → OPEN. V263 D579 equality:
OPEN → OPEN. Memory fidelity and advancing source-loop world threading remain
blocked on this construction. V370/L3, rdea-1/rdea-2/V400, V183 SUSPENDED(K-3),
and all endpoint/deployment conditions retained; no T field or premise added.
No compile, native/Kani run, extraction, host launch or new axioms audit.
Next normal ID **91222**, **74 attempts remain**, audits 91298–91299 unused.
Read-only source pin/anchor receipt: `evidence/pv-evhB-20261103/shared-vec-D580.json`.
