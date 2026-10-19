# Complete source accumulator constructor invariants

Candidate 12 is **not complete**. This checkpoint does not increment the
whole-candidate equivalence count.

`Accumulator::new`, `Variant::folds/final_len`, ZERO/ONE constants and all
carriers are byte-identical in the exact candidate, exact parent and frozen
production source. The complete constructor and length methods are emitted
with the original producer. The only external heap operation is bound to the
already emitted, exact `heap::filled` source, parameterized by the existing
reserve boundary. No template axiom or allocation-success premise is used.

`CuSavingsRhoAccumulatorNew.source_outcome` retains the complete outcome:
heap/reserve errors, runtime failures, divergence and the actual successful
record. `source_success` derives counter zero, power ONE and its canonicality,
RHS ZERO, the actual variant coefficient length (256 for S1, 64 for S2/D), and
length ≤256 from a successful whole constructor call. It does not assume
successful child calls or a length premise.

Canonical weight contents are deliberately **not** inferred from length.
That requires the actual reserve frame: an unconstrained reserve boundary can
return a modified vector before resize. The actual allocation/source resource
connection remains an explicit open requirement.

Combining the tail carrier with the heap helper exposed the original producer's
short global enum instance name `instDiscriminantVariantIsize`. The fix expands
only this attribute registration and qualifies the instance name. The original
and fixed ordinal reader functions print identically; the three 0/1/2 facts
are kernel-checked separately against the exact respective objects. Carrier
constructors and all generated Rust function bodies remain unchanged. Only
files affected by this dependency change were rechecked; existing arithmetic,
initializer and runtime regression suites were not replayed.

`RHO-ACCUMULATOR-NEW.json` and `RHO-POWER-TAIL.json` pin the complete current
focused closure. All accepted proof results use only standard
propext/Classical.choice/Quot.sound. Commands, revisions, features, exit,
wall/RSS/swap and exact axioms output are recorded. Source-only failures and
failed local proof attempts remain recorded separately, never accepted as
proof results.

The exact resume weight-decode loop was also isolated. Borrowing its Reader
in the helper hit the producer's nested-borrow limitation. Retaining both
original local owners (weights and Reader) instead hit InterpBorrowsCore.ml:984.
Neither emission is imported. The original first input is retained with its
failed receipt; the corrected ownership-preserving source kit is reproducible.
Further flag variations have no structural justification from these results.

Remaining: actual Prepared/resume dataflow and full weight traversal binding;
original optimized Option reborrow source binding; allocation-resource/frame;
complete accumulate/query and transaction observable-context composition.
