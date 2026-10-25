# Exact remaining native producer

The new primitive proof is useful but does not close actual heap::filled or
Accumulator::new. Both security targets remain not yet established.

## Before and required after

Before: Port21 emits Vec::try_reserve_exact returning arbitrary
`Result ((core.Result Unit TryReserveError) × Vec T)` with no post-Vec law.
The job does not alter that external, its template, or TrustedStd.

Required after, for the PINNED fresh Vec<QM31> or Vec<[u64;4]> path only:

Given actual valid native Vec header with len=cap=0, its native buf field
exclusively borrowed, a valid private Bump arena, the cursor word aligned and
in-bounds, and header/cursor regions disjoint, execute the literal RawVec path:
1. no growth when additional=0; return Ok, unchanged header;
2. checked-add/layout failure: return the actual capacity error, no ptr/cap
   commit and len unchanged;
3. nonzero allocation returning null: actual AllocError -> TryReserveError,
   no ptr/cap commit, len unchanged;
4. nonnull allocation: write returned pointer and cap=additional only into
   the actual RawVec fields; len unchanged;
5. abort: retain the actual executed ordered prefix, no returned Vec and no
   appended normal cleanup. Account rollback cannot erase earlier observations.

This statement does not assume initialized-content equality or whole-helper
output equality. Once len remains zero, its initialized index set is empty.
No capacity or physical whole-heap equality is requested by soundness transport.
No native no-oracle conclusion is taken merely from types or lack of Digest.

## Native admission and footprint, without fixed Rust offsets

For this cone only, native entry provides: valid Vec/RawVec header and exclusive
buf borrow; actual addresses of ptr, cap and len fields (Rust layout ordering
is NOT invented); private arena cursor address s with alignment8 and at least
one cursor word; arithmetic s+len < 2^64; cursor=0 or s+8<=cursor<=s+len;
prior live allocations above the cursor and separate from header; actual
cursor bytes read by the implementation. Valid Layout and nonzero size are
GlobalAlloc preconditions, not allocator-success assumptions. Normal field
writes use their actual native layout, not public account metadata.

Port22ARENA.candidate_word discharges the integer/body arithmetic link.
success_interval places a nonnull allocation below the old cursor and above
its metadata word. alloc_outside proves the eight-byte cursor store frame in
the byte-memory interpretation. fresh_reserve_length and fresh_reserve_empty
then derive the length and empty initialized range from disjoint store sites,
on every modeled prefix. Their premises contain no post-length equation.

Port22ARENA_selected_alloc_frame supplies NEW native evidence for the literal
SDK body, against Kani0.67's model, on a 256-byte aligned arena within34 usize
words: every arbitrary selected noncursor word is preserved, and returned
pointer/null, actual cursor store, alignment4/8 and success interval agree.
All nonzero valid Layout sizes are symbolic, including requests too large for
the arena; initial cursor may be zero or any admitted offset8..256. Null is
not excluded. Invalid/zero Layout does not reach GlobalAlloc::alloc. This
bounded arena/object model is not the deployed256KiB fixed-address arena.
It proves neither a Rust/LLVM/SBF ABI interpretation nor a complete memory,
ordered oracle-effect or abort-handler theorem. Unsupported constructs were
reported but verification has no reachable unsupported failure (1unreachable
check); original log is retained. No bounded check is promoted to universal
native source refinement.

## Reviewable implementation-specific proof route

Use the actual selected SBF sysroot/shim association for Vec<T,Global>, rather
than substituting the host extraction's Global or Kani's std allocator model.
First interpret just the cursor load/store and integer/pointer round trip for
this admitted arena, with exact eight-byte footprint and ordered primitive
prefix semantics. The arithmetic theorem is already available; the new native
check tests these operations in one concrete native object model. This is not
a request to certify general allocators, realloc, arbitrary headers, or Drop.

Then interpret the safe exclusive self.buf reborrow in Vec::try_reserve_exact,
passing len by value. In cap0, current_memory=None; finish_grow therefore
selects allocate, NOT grow/realloc/copy/dealloc. Connect the selected Global
runtime match: size0 yields dangling/zero slice; nonzero invokes the selected
alloc shim; NonNull::new turns null into the actual error. Interpret only
set_ptr_and_cap's ptr and cap stores, using actual field addresses from the
native Rust layout/admission. The dependent byte-frame theorem then supplies
len0 on both ordinary Result branches. The missing item is this selected
pointer/shim/field interpretation, not an unbounded general allocator contract.

On actual Ok, grow_exact has committed cap=n. For fresh non-ZST len0,
needs_to_grow(0,n)=false after reservation, so resize/extend_with's second
reserve cannot allocate again. Interpret its pointer writes and SetLenOnDrop
increments: n-1 clones then one final move for n>0; n=0 truncates0. Preserve
partial write/length prefixes on abnormal exit. Full QM31 derives Clone+Copy;
the unchanged Port21 emission returns the entire four-u32 self. The pinned
host array source uses SpecArrayClone<u64:TrivialClone> -> ptr::read of the
entire [u64;4], with primitive u64 clone=*self explicitly present. These are
source facts, not a claim that a pointer-read law has already been installed.

Finally use the literal Result::map_err match at core/result.rs962–970 and
the actual Allocation closures in heap.rs/verifier.rs. Error skips resize;
Ok continues with the actual returned Vec. No arbitrary reservation Bool is
introduced. This can feed the existing content theorem only after those
actual contents/outcomes are associated. Query accounting must still justify
every reached pointer/intrinsic/shim/abort leaf's ordered effects. Never infer
absence of RO calls solely from a carrier type. Port21's weaker probability
projection and independent all-outcome charge remain unchanged; privacy
cleanup is independently required.

## Approved policy scope and remaining trust

D157 explicitly excludes unsafe and allocation failure. D189's approved
SDK/private-allocator projection supports S2 account snapshots for its stated
scope; it does not supply general Vec len/initialized-content or oracle
history semantics. P2 supplies ownership/permissions/locking/rollback/
persistence; P7 links reviewed source semantics to the selected exact ELF.
Neither supplies a missing unsafe-memory interpretation by being named.
P6 concerns exact extraction/checking, not a hand-written word/byte model's
native association. No new trusted field, semantic axiom or policy extension
is installed. Standard Lean axioms only in accepted proofs. Release pins
remain the manager's default f8c0ec72..., devnet63ad3e9c..., Pool121f3e29...;
no new source-to-ELF identity gate or release coherence claim ran here.

The blocker is genuine and narrow: a finite-arena Kani check and an unbounded
integer/byte theorem cannot jointly manufacture the selected native Vec/ABI
interpretation. The final source/statement audit exposes exactly that gap.
No extraction allowance was spent repeating Port21's unsupported opaque shape.
