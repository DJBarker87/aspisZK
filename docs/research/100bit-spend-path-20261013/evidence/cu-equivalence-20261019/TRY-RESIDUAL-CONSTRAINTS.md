# Try/Residual constraint normalization and concrete dictionaries

Status: full normalized library LLBC passes strict symbolic borrow-checking.
Lean emission still fails at dictionary representation. The new concrete
infallible dictionary graph is checked; its generic frontend/source binding
remains OPEN. Production Rust is unchanged; COMPONENT-AUDIT has 88 targets.

The current Rust Residual<O> declaration requires its TryType to implement
Try<Output=O, Residual=Self>. Those two equalities are explicit in the pinned
LLBC Residual declaration's generic constraints. Rust Try also requires its
Residual to implement Residual<Output>, but does NOT assert that this reverse
TryType equals the original Try Self. The proof/model must keep these distinct.
The supported Charon remove-unused-clauses option explicitly warns that clause
erasure can be incorrect for operations justified by a bound; it was not used.

The earlier try_from_fn argument mismatch is created after method-signature
instantiation. A static sweep over the serialized types sees no occurrence of
that instantiated projection. The repair therefore runs after call-signature
substitution in InterpUtils.instantiate_fun_sig, before the existing input-type
checks. It recursively considers region-free parent projections only. For
each, it instantiates the source trait declaration's explicit generic type
constraints with the actual arguments and trait reference. A replacement is
allowed only when the complete instantiated trait reference and associated
type ID exactly match, extra projection arguments are empty, all binders are
region-free, and the replacement is region-free. Otherwise the old type is
retained. No trait clause, equality, input-type check or borrow check is removed.

`aeneas-parent-projection-constraints.ml` contains the helper. The isolated
frontend enables it with AENEAS_PARENT_PROJECTION_CONSTRAINTS=1. It includes
the previously pinned branch fallback and exact associated-type matcher;
the earlier frontends remain untouched. The full normalized library emission
now has no from_output input-type mismatch, mutable-copy error or loop
fixed-point error. It still exits1 at the backend Try metadata mismatch (two
source parents versus one backend parent), followed by unresolved identifiers
and recursive dictionary implementation output. Those failed declarations are
not promoted or imported. Attempt: array-trait-constraints-emission-a.

The 32-case capped regression includes:

* The 14 earlier compatibility cases with this new option disabled and enabled.
  Every successful baseline emitted file remains byte-identical and the
  unsupported mutable copies remain rejected.
* The full normalized library crate, with all original function bodies present:
  the old input mismatch remains when the option is off; with it on, strict
  `-checks -abort-on-error -borrow-check` succeeds.
* Two explicitly synthetic negative LLBC cases: the source Output equality is
  removed or given the wrong target. Both restore input-type rejection. The
  audit reconstructs the original pinned input from the wrong-target case and
  verifies that no other source field was changed in either mutation.

Every case has command, source revision, features, exit, wall time, RSS and
swap evidence. This is frontend/borrow-check evidence, not a compiled library
theorem; #print axioms is N/A. The dereference snapshot normalization is still
experimental and separately needs semantic admission or replacement.

The successful concrete NeverShortCircuitResidual/alias types and the exact
from_residual/from_output/branch methods are cut from the already pinned
emission, byte-for-byte. The failed cyclic dictionaries are excluded.
`emit-never-short-circuit.py --check` checks every source/output cut.

`CuSavingsTryGraph` supplies a productive graph representation: a Try node
retains FromResidual and a sequence of Residual-parent observations, each
carrying a Core Try with the declared output/residual types. Traversal consumes
a head and retains a tail; it does not require a nonterminating recursive Lean
record. Self and the parent's TryType are separate type parameters. The
concrete neverTry graph uses the exact extracted standard methods and a
constant parent sequence. Its parent equals itself, every parent observation
has the exact source methods, wrapping followed by branching returns Continue
of the original value, and the residual is uninhabited. These are checked
theorems, not axioms asserting whole-library equivalence.

New focused receipts: cu-never-types-a, cu-never-operations-a, cu-try-graph-a.
All three pass with #print axioms reporting no axioms for the audited
declarations. Wall1.60–2.01s, peak RSS below2.6GiB, zero process/cgroup swap.
Mapping the generic frontend dictionary emission to this representation,
including source type-constraint/coherence correspondence, remains required.
The graph alone does not admit a new standard-library implementation.

Resource review: the initial frontend build's outer reservation snapshot was
48.375GiB. The old controller failed to add the separate compiler container's
8GiB reservation before opening its compile gate; the projected total was
56.375GiB, so compliant aggregate admission was NOT established. That original
receipt and controller source are preserved as a resource-policy exception.
The compiler itself stayed capped6/8GiB with swap0, used RSS522848KiB and zero
swap. Low measured use does not waive the reservation rule.

The controller is now guarded before container creation, at the actual compile
gate and continuously while compiling. `verify-aeneas-reservations.py` rechecks
the same pinned source/cache with a 768MiB/1GiB controller and a separate
6/8GiB compiler, swap0 for both. Actual admitted/sampled reservations are
41.375GiB, below50GiB. The cached build succeeds and produces the exact same
frontend binary SHA256, with zero swap. This resource recheck is justified by
the missing admission evidence; unchanged Lean/runtime suites were not rerun.
Receipts: aeneas-trait-constraints-reservation-a and the inner
reservation-recheck receipt. The outer receipt supplies the exact task revision
for the inner artifact check. No foreign worker was stopped or modified.

Next: bind the frontend's newer dictionary metadata and concrete infallible
instances to the checked productive graph, then consume the complete emitted
initialization loop and prove builder equivalence. Unsafe primitive admission,
enclosing verifier/caller composition, all other candidate obligations and the
final soundness/privacy transfers remain open.
