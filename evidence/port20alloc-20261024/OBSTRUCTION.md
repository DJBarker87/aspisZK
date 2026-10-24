# Exact allocation join obstruction after focused extraction

The new unchanged-source helper emission is
`Port20ALLOC-generated/Funs.lean.txt`, lines 69–90. Charon LLBC definition 4
contains the actual generic source body. Definitions 2/3 contain the actual
row12/row10 calls to definition 4, including its generic arguments and concrete
Copy operands. `audit.json` retains those complete selected signatures,
generics, arguments and result destinations; `Port20ALLOC.llbc` retains all
bodies and cleanup branches. This is new extraction evidence, not a theorem
or a new frozen ELF identity gate.

## Native/extracted/approved carriers

Before extraction: fresh native `Vec<T>` contains pointer, length, capacity
and allocator ownership; `try_reserve_exact(&mut out,n)` returns
`Result<(),TryReserveError>`. The exact heap helper maps that actual error
to `r0::Error::Allocation`, uses `?`, then resizes with the concrete Clone
operand. Parent row12 subsequently maps core Error to probe Error; its full
Accumulator fields remain in the native/LLBC source.

After extraction (actual emitted declaration, not a requested law):

```
alloc.vec.Vec.try_reserve_exact {T} (A : Type) :
  Vec T -> Usize -> Result ((core.result.Result Unit TryReserveError) × Vec T)
```

The helper receives `(r,out)` from this external operation. It maps/branches
on **r**, and only on Continue calls
`Vec.resize copy.cloneInst out n value`. QM31's extracted real Clone is
`fun self => ok self`; the row specialization uses
`Array.Insts.CoreMarkerCopy 4#usize core.marker.CopyU64`. There is no scalar
replacement. The source kit has full four-word QM31 and four-u64 rows.

The approved `OraclePortStdAllocation.signature T` instead takes
`Usize × T × Bool`, returning
`Result (Except AllocationError (Vec T))`. The existing theorem proves that
*chosen interpretation's* contents and Allocation result. It supplies no
law assigning the external reserve pair to a particular native execution,
no law that its returned Vec has empty content, and no native ordered event
or private-state frame law. The source header explicitly excludes physical
allocation, capacity and Drop. D157 cannot add these laws: its exclusion of
allocation failure/unsafe is literal. D189 is the existing runtime boundary,
not a proof that this call's Allocation Err or cleanup can be erased.

Consequently the reserve-result observation can define a Bool only **after**
the actual reserve transition returns `ok (Ok/Err,out)`. `fail`, `div`, and
native abort/unwind are not values of that Bool. The helper content theorem
is total for either Bool; it does not by itself transport these other
outcomes or their prefixes. No successful-child premise was introduced.

This is an underdetermination of the extracted interface, not a production
counterexample: an arbitrary external reserve implementation may return
`fail panic` or `div`; the extracted helper propagates it, whereas the
existing interpreted filled result is `ok ...` for either Bool. Both external
choices have the emitted type. Even successful external choices may return
nonempty Vec content. Thus filling an external template with the desired
state/effect law would add a missing contract, not prove this native instance.
The raw external templates are retained as `.lean.txt`, never imported.

## Losses retained, not asserted proved

Charon's exact options record `hide_allocator=true`, `precise_drops=false`,
`desugar_drops=false`, and `skip_borrowck=false`. The LLBC still retains
conditional Drop/on_unwind/UnwindResume nodes. The Lean helper emission does
not reproduce that cleanup state. Aeneas's current ordered-declaration
closure emits the helper and specializations but omits the two constructor
declarations even though their structured LLBC bodies are retained. The
focused checker explicitly tests/report this omission. No backend/tool
patch, third extraction, Drop-erasure proof, logger, allocator stub or
external axiom has been installed.

The full native constructor Kani attempt keeps all three Variant inputs,
real allocation and destructor paths, all returned fields, and Err branch.
It timed out at 120 seconds (no OOM); no larger-cap or unchanged rerun.
Its log also retains unsupported-construct warnings, not dismissed as safe.
This establishes no constructor law. The separate capacity-overflow check
has a distinct nonallocating error shape; its result is recorded separately.
Neither check changes the all-source budget to accepted or S2-only inputs.

## Unchanged parent obligation

No source budget predicate, source constructor, protocol or verifier changed.
No producer is exported for Port17 OtherBudgets. Both row12 and row10 retain
the complete result/state/failure/divergence/rejected-prefix obligation.
The next concrete producer needs an existing-policy native reserve/cleanup
association with complete state and ordered events, followed by the actual
constructor control join. Reusing the approved whole-helper content theorem
does not supply the missing primitive association. If existing policy has a
separate primitive contract, identify its literal statement and instantiate
it; do not invent one. Port18 root/A cache work is independent and untouched.
