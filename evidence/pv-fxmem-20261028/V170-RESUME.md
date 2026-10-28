# V170 finite consumed-type source law (D362 resume)

Target not yet established. Generic finding retained unchanged.

Before: a world-independent polymorphic callback reproduces the complete
native drop result for every T and accessible world. This is false, as proved
in PV_FXM_DropCounterexample; no generic closure is claimed.

After: exactly the single explicit op4 site in ProverRwFullFuns, line 16098,
Rust host_tree.rs:29, consumes Vec<u32, Global>. DROP-INSTANTIATIONS.json gives
the complete emitted occurrence list and selected-dictionary assignment census.
The dictionary forwards the same polymorphic field and adds no new op4 calls.
This is an explicitly narrower statement, authorized by D362.

u32 has no user destructor. Vec<u32> is not drop-free: Vec drops the slice,
then RawVec calls Global deallocation iff capacity is nonzero. The size is
4*capacity, alignment 4, independently of length. Even an empty Vec with spare
capacity frees once. The world consumes the allocation identity; it does not
return an empty live Vec or claim to wipe freed bytes.

PV_FXM_DropWorld proves the source/reference equation, exact deallocation
history/counters, no element-destructor calls, logical snapshot/disjoint-frame preservation and
caller composition in the post-drop world. PV_FXM_Physical additionally carries actual physical bytes and every allocator-
accessible external effect in Runtime. Deallocation does not promise physical
bytes or accessible external state unchanged. The old memory field is a
logical allocation snapshot, invalid after live=false. This interpretation is
explicit, not a physical memory-preservation assertion.

The allocator's private state is
an explicit parameter and transition, not discarded. Buffer address/capacity
are runtime metadata, not inferred from the extracted list. The source law
uses the returning System deallocation primitive; libc allocator internals,
nonreturn and machine side channels are not proved by this library gate.

PV_FXM_DropSelected installs op4 only at alloc.vec.Vec U32, retains it at every
other type, and proves that restoring op4 recovers the entire original record.
Its projection returns ok (), and execution threads the world effect to the
caller. It works for any base ExternalFuns, including the selected dictionary.
It does not modify the actual frozen dictionary or any endpoint theorem.

STRUCTURAL-DROP-GATE.json token-checks the complete pinned nightly source
chain, including current_memory's zero-capacity condition and layout. Evidence
class: structural (K-1 substitute), over the explicit allocator primitive.
The optimized drop-u32-03 run passes 260 paired finite cases: actual mem::drop
versus owned ManuallyDrop/slice-drop/dealloc reference, exact pointer/layout,
0 alloc/realloc, free iff capacity > 0. This is finite validation.

Focused world compile 35503 and installation compile 35505 pass. All printed
axioms are subsets of propext, Classical.choice, Quot.sound. Failed attempts
35502 and 35504 remain as rejected evidence. Receipts contain timing/RSS/swap
and exact source revisions. No Kani, ELF rebuild or endpoint premise removal.

Disposition: finite consumed-type library law and installation supplied;
generic row remains refuted, and deployment/allocator primitive realization
and L1/L2/L3 side-channel obligations are retained. Do not count the latter as
new T fields or as discharged endpoint premises.

Semantic library Drop entries are one Vec::drop and one RawVec::drop per
consumed vector; primitive u32/Global have no user destructor. The counter
field elementDestructors counts element/user glue, not emitted machine call
instructions. Allocator-internal effects are inside Runtime.
