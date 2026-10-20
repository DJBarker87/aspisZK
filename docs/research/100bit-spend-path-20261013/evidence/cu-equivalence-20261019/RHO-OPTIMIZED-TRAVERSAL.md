# Source coefficient traversal and materialization (2026-10-20)

Candidate 12 remains open at transaction level. This closes the previously
blocked optimized coefficient-loop source binding, and composes it with the
reference loop and actual final materialization.

The user authorized producer repair after the earlier scope impasse. The new
producer uses the pinned b59d5188 source archive from the existing native tool
build, with exactly two source changes recorded in
`tools/cu-equivalence-20261019/rho-borrow-producer-repair/producer.patch`:

- Interpret optimized MIR mutable-reference Copy as a fresh reborrow/loan,
  preserving exclusivity rather than duplicating a mutable borrow ID.
- Ignore an ancestor loan projector when collecting a deeper given-back layer;
  retain errors at the relevant layer and for active borrow projectors.

All extraction checks remain enabled. Charon unconditionally resets MIR
optimization level to zero, explaining why earlier optimization-level flags
left the std call intact. Explicit Inline/ForceInline passes allow the exact
concrete `value.as_deref_mut()` wrapper to inline its std dependencies. It then
emits the whole three-result helper successfully. The wrapper Funs is imported
bytes-unchanged, with only an identical raw/terms carrier alias. This is the
actual standard-library method expression, not a branch-normalized surrogate.

The optimized loop keeps its original emitted bodies and term increment. One
concrete opaque callee occurrence is specialized to that emitted wrapper;
reversing this substitution restores the raw selected declarations exactly.
No compatible hand-written triple API or template axiom is used.

Checked results:

- `CuSavingsRhoSourceOption.source_outcome`: complete view and both handbacks,
  including Some/None behavior.
- `CuSavingsRhoOptimizedTraversal.source_eq_some`: whole optimized loop equals
  the existing bounded arithmetic batch. Push failures/divergence and counter
  overflow are preserved; diagnostic index bounds are explicit.
- `CuSavingsRhoSourceBatch.source_both`: the actual optimized/reference loops
  and actual finish return the same canonical coefficients under the existing
  local arithmetic invariants. The source basis supplies coefficient admission.

All successful Lean results use only `propext`, `Classical.choice`, `Quot.sound`.
Exact commands, source/object/cache pins, features, revisions, exit status,
wall time, RSS and swap are in `RHO-OPTIMIZED-TRAVERSAL.json` and its receipts.
`check-rho-optimized-traversal.py` verifies source generation, specialization,
current source hashes, dependent import objects, and these axiom audits.

The remaining goal is actual accumulation/caller and transaction composition,
resumed-weight canonicality, and the reserve frame/sufficient-resource
connection. Production Rust, protocol, fixtures and CU measurements have not
changed. No new CU/runtime/SBF replay is justified by these proof-only changes.
