# Arbitrary byte generation remains OPEN

The dynamic valid initialized one-window allocator harnesses pass their exact
native wrong-length result assertions and matched inversions (K010–019).
An additional all-payload attempt uses a weak verified no-op modifies contract
solely as input generation. It replaces no production callee, copy or arithmetic.
This route is NOT usable in the tested configuration:

- K026: purported positive contract fails CAR size is less than
  __CPROVER_max_malloc_size (one failed check).
- K027: inverse postcondition and that same CAR check both fail; excluded as
  a matched semantic control because of the second failure.
- K028: stub_verified on the mutable-slice helper causes a Kani compiler ICE in
  reachability.rs:419, failing to resolve IntoIterator for nested slice reference.
  No solver proof or matched caller-control credit.

The helper is therefore unverified. No arbitrary_long candidate was submitted,
no decoder received an unverified replacement, and no source-closure claim uses
these results. Restricting allocation length to repair CAR would add a bound
not justified for the all-length task; replacing a slice by a one-byte pointer
would lose the required arbitrary-payload coverage. A new representation would
need independent fidelity controls. This is a harness/tool limitation, not a
counterexample to the five frozen early guards or a shipped SDK defect.
