# Shared typed memory and ownership interface

Written before any PV_OWN_ Lean source. Base 6a2c273f22, prover candidate
1a3cd3de26 with parked world merged; no implementation changes.

## Carrier and refinement

Reuse PV_W_Threading.Run/M, including the post-world and complete prefix on
error/divergence. The process carrier must retain W-CARRIER-1 state: statics,
atomics, allocator internals, thread-local state, unwind flag and extra native
state. PV_W_Enriched.World supplies that carrier. A heap maps allocation base
addresses to live layout/initialized-byte/owner records. An allocation identity
includes a generation; address reuse does not revive a stale owner. Layout
contains actual size and alignment, not the requested new allocation size
mistaken for every existing allocation's size. Disjointness compares BOTH
live allocation sizes (the legacy BoxAdequacy same-request-size formulation is
not a sufficient heterogeneous-heap invariant).

Typed views are relations, not a second independently writable object map.
A codec specifies size/alignment and representation, permitting padding bytes
to remain uninitialized. Vec<T> relates pointer/capacity/length and initialized
prefix cells to one allocation; Box<T> relates one live object; arrays relate
contiguous elements; String adds UTF8 validity of the initialized length.
A valid heap has nonoverlapping nonzero aligned live allocations. Byte writes
are range checked; typed read requires initialized representation and a current
read permission. Typed write requires exclusive permission and preserves the
allocation header, owner, and all out-of-range bytes. Moves consume a source
slot and install the same generation at an empty destination. Shared borrows
prevent mutation/drop; exclusive borrows prevent all competing access; release
restores the original owner rather than fabricating a new allocation.

## Operations and trace

Allocation has explicit success/null/error/divergence branches and retains the
allocator post-state. Success installs an uninitialized allocation. Initialization
changes bytes only. Growth consumes the proved reserve-family request/result
law, copies the initialized prefix, transports the ownership generation and
invalidates the previous live identity only on success. No-growth has no request.
Truncate updates length before dropping the removed suffix, and never changes
capacity. Failure/unwind uses the actual type-specific continuation.

Drop is not universal. Instantiate separate sequences for POD Link (all kind
and endpoint fields retained), u16, the sparse (usize, WideExact) tuple, String,
Vec of each, and relevant Box/array carriers. POD element drops emit no runtime
call; Vec glue frees its capacity layout after element glue; String delegates
to Vec<u8>; stack arrays have no heap free. MIR at the deployed configuration
is the authority for actual glue order, including owned Path::join arguments
and partial temporaries. A modeled event sequence is not a native binding.
Every primitive event records its own pre-world, and abort does not execute an
unwind suffix. Do not erase an internal event from D159 without the existing
observer's required frame/public-factorization proof.

## Evidence and trust

Lean will prove generic byte/ownership/range/frame/continuation laws and explicit
per-type model sequences. These are mathematical model laws until a checked
source binding is supplied. Source inspection, token/AST matching and MIR pins
are structural evidence; same-input native tests are finite validation. A
structural K-1 substitute additionally needs a complete Result law and native
differential; matching snippets alone never restore a row.

Any step resting on Kani, Aeneas or Charon agreeing on Rust semantics is
**reclassification within existing tool trust**, never premise removal.
New extraction must obey (x'): pinned extractor toolchain, deployed features,
release settings, deployed lock, and comparison of reached std bodies with
1.94.1. Native differential uses deployed 1.94.1. No Kani is authorized here;
no quarantined function-pointer or copy-dependent PASS is consumed.

rdea-1 retains allocator/runtime primitive adequacy, including outcomes given
prior state, fresh aligned nonoverlapping returned ranges, realloc byte-prefix
preservation, actual deallocation and default failure handlers. These are the
existing runtime item, not new T fields. Byte stores, typed ownership and concrete
glue sequencing remain proof obligations, not allocator assumptions. Compiler/
executable D381/D386 boundaries remain. T is exactly entropy_law, entropy_kernel,
observation and is unchanged.

## Consumer acceptance order

V229 first: full typed Link carrier, every in-place write/read restoration,
FlatMap specialization, ownership transfer and destructor suffix, composed with
PV_RDB2D_CollectorProgram.complete and its value law. Then V230: native
usize/u16/stack-array association and same returned Vec drop. Then V239: sparse
Vec byte initialization/ownership plus its remaining raw arithmetic, builder
and public consuming-call laws. Then V178: owned name/move/join cleanup and
remaining deployment diagnostic reachability. Each row remains SUSPENDED until
all consumed facts hold. Witness-dependent occurrence/order/size of any
allocation or destructor event is a FINDING: stop that row, retain evidence,
never restrict the witness or weaken D159.
