# Paired source relation and its precise boundary

This is an explicit sequential Rust source argument, pending the prepared native
check. It is not an assumed output-equality premise, a compiler-correctness,
hardware, arbitrary-provenance or OS-world theorem. No Lean model is promoted
to that theorem. Native erasure closure remains unproved until an accepted
native operational proof covers the listed boundaries.

## Stores and steps

Original O and instrumented I run identical selected items (apart from their
private module prefix and dependency resolution). A related pair consists of
identical live source locals, initialized payload bytes, move/drop flags, control
locations outside a hook, boundary-provider state and result aggregates. I also
has disjoint statics J/COUNT/OVERFLOW/E0/E1/E2 and hook-local Copy scalars.
Projection deletes only those statics and hook-local scalars. This is a relation
on operational source stores; it is not a law for an OS World or arbitrary
ledger-after. Initial source stores are identical; no output fact is a premise.

For an original source step, the corresponding I instruction is byte-identical
and has the same source operands. The selected code never names the ghost
statics. At a hook, a shared borrow of self.0 is created while Drop's unique
borrow is live. The temporary shared borrow ends before self.0.zeroize(); the
posthook's borrow starts only after zeroize returns and ends before Drop returns.
Only Copy u8 values escape, never a pointer/reference to self. No child pointer
is held over any source move. The ghost functions make no call back into source
code, allocate nothing, have no user Drop, and perform no volatile operation.
Projection maps those finitely many reads/local operations/static writes to
stuttering. The actual original mutable Zeroize call is one matched step sequence,
including its iterator and scalar volatile writes/fence. Nothing replaces it.

This gives the sufficient forward/backward stuttering argument for normal
sequential source executions, including identical returned values and source
frame, PROVIDED the source semantics supports the stated disjoint allocation
and typed-loan rules. Those are the exact semantic facts to check in the native
producer, rather than a whole-result premise. It makes no concurrency,
signal/reentrancy, panic-unwind, memory exhaustion, hardware, register/stale-copy,
or timing claim. The prepared Kani check tests the concrete memory model under
its primitive stub; it cannot by itself establish general Rust provenance.
The static-mut API is job-private in use, sequential and never reentered; it
would not be admissible as an unrestricted multithreaded library API.

## Total ghost operations (even beyond the selected normal paths)

initialize maps every u8 to j<32 by remainder32. There is one call at harness
entry, before any owner is created. coordinate only reads J. The array observer
tests N in{32,64} and j<32 before indexing. Thus j<N, and when N=64, j+32<=63;
addition cannot overflow usize on the pinned64-bit target. The observer's
unsupported scalar/type/range paths return len0, without expect, panic, unsafe
casts, recursion or loops. Its two u8 reads use the existing typed indexing;
len32's high byte is the constant0. Supported selected arrays resolve through
Zeroize for[u8;N], the DefaultIsZeroes blanket implementation and the explicit
u8 byte method, which always returns Some(*self).

record pattern-matches COUNT:0/1/2 assign a separate event static then literal
1/2/3; any other value sets OVERFLOW. There is no count arithmetic, indexing,
capacity panic or wrap, even from an invalid prior count. Each event consists
only of Copy usize/u8 values, no alias, destructor or address. events copies
three fixed scalar events, no indexed log. Three normal Drop calls fit exactly;
the fourth would set overflow rather than alter source behaviour. Sentinel and
overflow assertions belong to the harness, outside the original source path;
none is inserted into Drop. The selected normal path census below excludes
both. Logs and reads are secret ghost observations, erased by projection; no
claim about physical erasure of ghost copies is made.

## Actual roles and moves (identities do not derive from values)

See source-role-map.json and the separately captured MIR binding evidence.
Use source places and move/drop flags as identities within each execution;
relate places across O/I structurally, never by equal event bytes or addresses.

1. draw's local bytes:Zeroizing64 is moved into Draw.bytes. resume destructures
   self into request, bytes and outcome; the aggregate's moved-from storage
   has no remaining byte-owner drop. No pointer/identity needs to survive that
   move. The currently live destination place supplies Drop's hook borrow.
2. Err returns before constructing field or leaf. Exactly bytes64 drops. The
   error is moved unchanged through From into Os; request has no Zeroizing field.
3. Ok creates field32 BEFORE leaf32; both are distinct local owners even when
   equal-valued. copy_from_slice copies disjoint halves into those places and
   has no user Drop. Rejection increments request.retry (entry<=15, result<=16)
   before constructing the return value and exiting the scope. Reverse local
   cleanup is leaf32, field32, bytes64. The retry comparison distinguishes
   More(entry+1) from Done/RepeatedZeroBlock. Returning More moves only request.
4. Acceptance moves field and leaf into the respective named Secrets aggregate
   fields in Ok(Some(...)); their local drop flags become unset. bytes64 drops
   before resume returns. At phase(success), the returned aggregate owns both32
   fields LIVE; it has not been disposed. run then moves that aggregate into
   owner, reads its j coordinates while live, and calls drop(owner). Struct
   fields drop in declaration order: nonce has no destructor, then field32,
   then leaf32. These are the destination field roles after moves, not the
   moved-from local addresses. The success phase is distinct from disposal.

All normal paths therefore have either1 or3 events including explicit disposal;
no normal path can fill a fourth slot. Semantic identity is the above source
place history, NOT event index, byte equality or a ghost invocation ordinal.
A MIR binding supports this normal-path map but is not a source-to-native
refinement proof. Unwind branches are retained in MIR; no new panic theorem is
claimed. Role association does not depend on uniqueness of F,L or nonce.

## Concrete quantification and frame

Before/after contract is unchanged from SOURCE-CONTRACT.md in resume-p6,
renaming only the prospective private prefix. Complete arbitrary nonce32,
postbuffer64, entry0..15 and every valid NonZeroI32 Ok/Err remain. Pairing uses
one identical supplied primitive outcome for both executions, not freshness,
independence or an OS error schedule. For every j<32 it checks result/control,
nonce/field/leaf coordinates, real destructor observations and ghost-frame
preservation through the original execution. Coordinates j and j+32 cover all64;
they do not quantify over only equal/zero/fixture buffers. The final-slot target
is checks::paired_coordinate_native_resume, with unwind66, solver kissat,
stubbing getrandom::fill only, extra-pointer checks and unwinding assertions.
It is PREPARED, not run. No executable launcher is supplied: ZERO Kani this job.

E1 remains literal contextual successful64; ledger stub NEXT/LEDGER is not an
OS World. Native fill association/error transport, whole driver reachability,
finite16, outer8 adaptive public policy/durable ledger/full transcript and
L1/L2/L3 remain. Both deployed targets not yet established.

## Observed evidence boundary after admission denial

The one new MIR compile was denied before go/launch: finite reservations plus
new8GiB were34762391552B (<55GiB), but uncapped resident31026192384B plus7GiB
OS/control failed the physical-reserve gate. No retry is permitted this step.
Thus no new MIR result, native compilation or harness typecheck exists here.
The cfg(kani) harness is prepared source, unexecuted/unvalidated.

Read-only inspection of old054 emission-audit.json binds request2, bytes3,
field10, leaf12 and normal precise Drop sites430/441/448 and544/555/562 (leaf,
field,64), with shared final64 site607. Retry add/write380/382 precede those
rejection drops. Exact statements/spans/type/trait arguments are retained in
reused-bindings.json. This is reused source assessment only, not a new identity
gate. The complete metadata source_text matches selected resume under prefix
rename. However its recorded accepted branch at the exact nested If/1 path is
an EMPTY statements list. It does not supply the required success aggregate
move/returned-field witness. We stop that reuse item; this observation does not
claim the actual Rust success path is empty, impossible or verified. Native
success/disposal role binding remains source-inspected only. The old014 projected
trait Drop obstruction remains unchanged and is not retried.

Coordinate/capacity Lean lemmas certify natural-number bounds and extensional
coverage only. The source-role and stuttering argument above remains an inspected
argument in the intended sequential typed-store semantics, not an implemented
formal semantics or mechanized native projection theorem. No premise was
removed. A concrete accepted producer for that semantic relation is an actual
blocker before the final-slot result can establish the full native P6 contract.
