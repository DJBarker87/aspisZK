# Port20ALLOC interface design before extraction

Base: `17d459f0326cff8aa9f55e2629937ca4c5345851`. No shipped change.

The native helper has inputs `(n: usize, value: T)` and a private fresh
`Vec<T>`; `T = QM31` (four u32 words, full source Copy/Clone) or `[u64;4]`.
The native first transition is `Vec::new`, then the **actual**
`out.try_reserve_exact(n): Result<(),TryReserveError>`, then `map_err`/`?`.
On Ok, `resize(n,value)` uses the concrete Clone implementation; on Err the
owned vector is dropped and `Error::Allocation` returns. Allocation state,
capacity, pointer ownership, allocator abort, and destructor behavior are
native runtime concerns, not fields of Aeneas `Vec.val`.

The already installed interpretation is
`OraclePortStdAllocation.implementation T heapFilledSite (n,value,reserved)`.
It returns `Program ... (Result (Except AllocationError (Vec T)))`.
Its source `filled_exact` supplies content `replicate n value` on **given**
true and Allocation on **given** false; `filled_cone_join` relates two
chosen interpreted Programs. Neither binds `reserved` to native state.
`CheckpointBytes3Allocation.filled` maps this to the extracted verifier
Error carrier without discarding Err. No helper premise says that arbitrary
native execution has no oracle calls or preserves an ordered log.

Required association, not assumed: after identifying actual typed state at
entry and exit, native reservation Ok maps to true and Err to false; native
outer fail/div/abort keep their full prefix and result classification. Clone
must produce the same four words without an oracle interaction. Each native
step must preserve the complete ordered oracle log relation and private
allocation/account separation. Do not replace this with equality of returned
content, an arbitrary Bool, or a `noHash` field.

Existing policy scope: LOG D133 approves documented BTreeMap semantics;
D157's pure-std extension **excludes** "I/O, allocation failure, concurrency,
interior mutability, hashing ... or unsafe code". The named heap interpretation
is already present in `OraclePortStdAllocation` and the S10 inventory; this
job does not extend it. LOG D189 retains TrustedStd plus the runtime allocator
premise (allocation failure aborts the transaction) for the SDK snapshot/
cleanup boundary. That is not permission to erase this helper's explicit Err
or certify allocator internals. Physical allocation/capacity/Drop remain open
under the existing runtime policy.

Row12 parent: `Port3_Constructor.extracted` calls finalLen, zero, filled with
the concrete Copy record, map_err, branch/residual, then zeroWide/one on Ok.
Its complete result is `Result (core.result.Result Accumulator Error)` with
weights, rhs, power, next. Every Variant S1/S2/D remains in scope (lengths
256/64/64); no success restriction. Row10's full parent includes its mutable
index loop and all raw/terms fields; the length64 reference theorem alone
cannot supply its all-input local budget. It is contingent on closing the
same native helper boundary, then separately associating its loop effects.

Before and after proposed budget predicate (unchanged):
`forall {A} (op : Call A) H, operationId op in
[3,4,6,7,9,10,11,12,17,19] ->
length (eval H (rest op)).1 <= w (operationId op)`.
No new actual `rest`, budget, producer, or premise change is installed.

Extraction will inspect the actual unchanged helper, including reserve's
result, concrete Copy/Clone operands and native private state. Monomorphizing
entry wrappers only expose the full types; they are not source-progress or
zero-read theorems. If extraction fails at private Drop/allocator state, retain
that failure. Kani's normal successful-allocation model would not establish
universal allocation-error coverage; no such check can close the join alone.
