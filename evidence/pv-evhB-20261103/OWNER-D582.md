# D582 owner construction: exact current boundary

Resume: `9f6c615e29`, branch `codex/pv-evhB-20261103`. This is a partial
construction, not discharge of `reached_reserve_header_delivery` or the v263
descriptor-view instance. The unchanged statements remain in
`../../BLOCKER-evhB.md` and `../../SHARED-VEC-D580.md`.

## Descriptor ownership and source slots

`PV_EVHB_RawVecOwner` uses the actual V183 `World` family. Its allocator
parameter is `Heap S`, containing backend state and a pointer-to-layout
metadata table; its frame is `Frame F`, containing the existing frame and an
explicit source-slot table. A `Header` has pointer, **stored RawVec capacity**,
length, element shape, and evidence of the source dangling-pointer constructor.
`Owned` is exactly allocation metadata for `cap * width` and the element
alignment with `world.live pointer = true`, or dangling with stored capacity
zero. Length validity and initialized element interpretation are separate.

The slot key comes from a source place, not erased elements. `store` and
`install` preserve that key; `move` transports the descriptor between places.
This does not yet construct the original callers' places, lifetime identity,
uniqueness, constructor allocation of identities, or receiver-to-place map.
In particular, a `Nat` parameter named `owner` is not itself evidence that it
denotes the receiver of a reached Rust call. These missing associations are
not inserted as a new compatibility field or trust item.

## Source phases that cannot share one live-header invariant

Pinned Rust 1.94.1 RawVec SHA256:
`0c006d1bedcc8c1aa6d8f37ad5553e1b14c452c732745612cf23c4663c090965`.
`finish_grow` at lines 527 onward takes `&self`, performs allocation/growth,
and returns the pointer without changing the header. `grow_exact` and
`grow_amortized` call it with `?`; only success reaches `set_ptr_and_cap`.
That function stores the pointer at line 745 and capacity at line 746.

For a moving successful realloc with positive old capacity, the old pointer
is no longer live before those stores. For in-place growth, the allocation's
exact layout has changed while the old capacity has not. Thus `Owned` of the
OLD header is not a valid invariant at the return of this internal helper.
`Pending` owns the returned allocation; `pending_install` derives `OwnedAt`
after the two stores. This is a phase distinction, **not a counterexample to
ownership or header delivery at the enclosing reserve's return**. No reached
counterexample to either requested final equation is claimed.

`deallocate` at lines 842 onward explicitly does not clear pointer/capacity;
Drop consumes ownership. `deallocate_consumes` records this, rather than
claiming the old descriptor still owns freed storage. Zero-capacity/ZST
deallocation is skipped by the source control model.

ZST handling requires two capacities: stored RawVec capacity is zero, while
`capacity()` returns `usize::MAX` (lines 621-622). The ownership relation uses
the stored capacity. `RawVecSource.capacity` exposes the public capacity.
There is no claimed counterexample based on conflating those capacities.

## Constructed control and explicit world projection

`PV_EVHB_RawVecSource` is a source-shaped control model for exact/amortized
growth, reserve, allocation/error mapping, header commit, grow_one, drop, and
the two branches of handle_error. It retains inner allocation denial and all
outer Result/fault/divergence/exhaustion variants with their returned worlds
and ordered events. `exact_success` and `exact_denied` are derived from a
primitive allocation answer; no whole-reserve answer is a Runtime field.
Primitive Global/System and diagnostic bindings remain open, as do shrink
and push's value/length stores. Natural arithmetic is interpreted on admitted
ABI/source-valid states; the full checked/wrapping/layout transport is open.

`PV_EVHB_RawVecProjection.eraseSlots` is an explicit map between the world
types. Allocation/denial commute with the existing V183 updates. Source
header installation changes the source table and disappears under this map.
`execute_frame` proves that V183's existing execute does not change its frame.
Consequently the new source table cannot just be read from that unchanged
frame to discharge the requested post-world metadata equation. The source
identity/current-call association must also be recoverable after projection,
for example by an allocator-side owner registry with a proved returning
projection and a pending/committed phase interpretation. Merely declaring
such a registry, or defining its answer to be `Execution.buffer`, would not
prove the source association.

The exact next construction is that source-derived registry and selector,
initialized at the original constructors and preserved through their moves
and calls. Prove its correspondence to the actual native receiver and header
stores, then derive the unchanged reserve equation and v263 instance. The
source-slot model here supplies local store/phase laws for that construction;
it does not supply the selector as an assumption.

## Evidence and retained obligations

`owner-source-d582.py --check` checks ten exact source spans, source hashes,
the ordering of successful header stores, absence of header stores in
finish_grow/deallocate, and the new control model's branch fragments. This is
**partial own-1 structural evidence**, not a machine source-correspondence
proof. Per-attempt receipts determine which Lean sources are accepted; failed
attempts with `sorryAx` earn no credit.

Allocator metadata transitions are returning-allocation semantics, not proof
of actual allocator/kernel adequacy. rdea-1 remains an obligation; rdea-2,
V400, V370/compiler preservation, L3, V183 SUSPENDED(K-3), and the complete
native failure/diagnostic association remain unchanged. No T field, endpoint
premise, release source, artifact or deployment condition is changed.
