# V183 allocator-world source law (D362 resume)

Target not yet established; no deployed endpoint premise removed.

Before: op32 was an unspecified, fixed world-free callback, without allocator
success/error/capacity/data laws. After: an explicit world-indexed family of
original-carrier ExternalFuns dictionaries projects the native/reference
execution. Only op32 is updated, and restoring it recovers the whole record.
This is not advertised as one fixed dictionary reproducing every allocator
world, or as a stateful whole-prover refinement already installed at the endpoint.

The four emitted sites are recorded in STRUCTURAL-RESERVE-GATE.json:
prover::derive_private_salts (Vec<[u8;32]>), EncodingDomain::encode
(Vec<Vec<T>>), encode_commitment_words (Vec<Word>), EncodingDomain::new
(Vec<Vec<M31>>). Each starts with Vec::new. The source law also covers general
valid buffers, with effective Vec::capacity, including the ZST sentinel case.
Runtime shape and buffer identity/capacity are explicit metadata, not inferred
from the extracted list or fixed by an assumed ABI theorem.

ReserveWorld proves native/reference equality, preservation of every value
and length on all outcomes, no-growth identity, requested capacity/pointer on
success, and exact requested layout on AllocError. CapacityOverflow occurs
before an allocator call on zero-size overfill, checked-add overflow or invalid
repeated layout. AllocError is an inner Err, not panic or unconditional success.
Failure preserves vector/header/live allocation and logical data snapshot,
but retains the allocator's changed private state, attempted-call counts and
ordered request/response history. Success is exactly one allocate or realloc;
no explicit element Drop or direct deallocate is performed by this operation.
Allocator-internal effects, including any internal frees or destructor work,
remain in the complete allocator Runtime, not silently set to zero.

ReserveFacts proves exact attempted counts/history and allocator state on
both branches, copied logical allocation bytes and uninitialized spare bytes,
preservation outside the destination, and buffer nonvacuity. These logical
snapshots are distinct from physical freed storage: Physical.Runtime carries
actual physical bytes and all allocator-accessible external state, and its
projections retain exactly the raw allocator step's output on success or error.
A separate disjoint frame is the only frame claimed unchanged.

ReservePrimitive exposes exactly the source primitive signatures. Fresh
allocation receives only its layout; it cannot depend on an unused old dangling
pointer. Growth uses the old pointer/layout and new size. Layout equality
excludes the changed-alignment Global fallback; the zeroed flag is false.
ReserveLayout proves wrapping-subtraction, padded-alignment and checked-product
normalizations. usize_exact proves admitted error sizes encode without wrapping.

ReserveSelected keeps the original error carrier. Its type-identity argument
is precisely the existing selected op5 installation; encodeError maps to the
source-extracted CapacityOverflow or AllocError { layout, non_exhaustive: () }.
error_payload proves the cast transports the entire source error unchanged.
Its caller theorem passes the post-attempt state through both success and Err.

The structural (K-1 substitute) gate checks ten complete pinned alloc/std bodies
and four complete core Layout bodies; every model/source difference is listed
and assigned a symbolic lemma. The optimized reserve-05 differential passes
2,160 paired cases covering no growth, allocate/reallocate, injected null,
capacity/layout overflow, ZST, and non-Copy elements. It checks complete inner
error kind/layout, all values, len/capacity/pointer retention and explicit
allocation/reallocation/deallocation/element-Drop counts. Finite validation only.

The source law shares the same explicit native raw primitives with its owned
reference. It is not an unbounded libc implementation, compiler or deployed
binary proof. Primitive realization in the deployed artifact, failure-event
witness independence, real RunJoin and L1/L2/L3 obligations remain P, never T.
No observer/simulator weakening or new trust field is introduced.

Focused accepted targets: ReserveWorld 35515, ReserveFacts 35520,
ReserveLayout 35522, ReserveSelected 35524, ReservePrimitive 35525,
ReserveCaller 35526, Physical 35527. Full header/state composition is the
ReserveCaller theorem; the earlier value/world-only projection is not used
to claim capacity has been passed to the caller.
