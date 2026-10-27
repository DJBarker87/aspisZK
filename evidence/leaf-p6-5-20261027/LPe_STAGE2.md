# Prepared claim splits

K008 PASS: actual powers::<2> on arbitrary canonical E equals
[ONE, ONE.mul(x)], with nonzero high-limb cover. This is a two-entry prefix
lemma, not the seven-entry caller result.
K009 TIMEOUT90s: first coordinate of powers::<3>'s last entry versus
ONE.mul(x).mul(x), arbitrary canonical E. Replaces the inherited whole-array
three-entry timeout with a smaller assertion, not a restricted coefficient.
K010 TIMEOUT90s: actual canonical::Q::raw all four limbs versus the explicit
wrapping u64 formula; canonical independent operands. Retained as an open cut.
K011 TIMEOUT90s: private sum update versus explicit wrapping sum formula.
K012 FAIL: builtin memcmp unwinding (array equality, 16 bytes, unwind6),
not a discovered arithmetic counterexample. K013 replaces the array equality
with four coordinate assertions; no resource or unwind cap is raised.
No raw product law follows from a passing finalizer.

All native modifications are cfg(kani) modules inside the scratch source copy.
No research crate or program source was edited. The complete seven-power,
reached wide Dot state, source-order six-point/private-body composition, and
same-execution P6 implementation refinement remain open until their own laws
are established. No top premise is replaced by a result certificate.

K013 PASS: all four native finalizer coordinates match the explicit two-fold
Mersenne reduction on arbitrary u64 sums; MAX high-sum cover reached. This
closes the private finalizer source cut only, not the reached public Dot join.
