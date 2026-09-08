# Bounded Gao recovery and the circle-to-coefficient endpoint

This records the completed mathematical work preceding the user's pivot to
the NUC [performance prototype](performance-review.md). It does not claim
an accepted-proof extraction theorem.

`GaoRecovery.decoder_complete` proves completeness of the specified
finite-fuel Euclidean decoder on **arbitrary received values** within
`floor((n-k)/2)` errors of a degree-below-k polynomial at n distinct points.
The theorem derives the interpolation/vanishing-polynomial initial invariant,
its preservation, strict degree descent, nonzero locator, key equation and
exact quotient. It does not assume that decoding returned successfully.
This is a mathematical model using Mathlib polynomials (in a noncomputable
section), not an extracted implementation or a measured efficient extractor.

`GaoC1Recovery.recover_coefficients` composes that theorem with the previously
proved natural circle/Laurent embedding: scale by z^512, decode a degree-at-most
1024 polynomial, unscale at the public target points, then apply the public
inverse matrix. Under distinct circle samples, the declared error radius,
and a checked public left-inverse premise, it returns the coefficient vector.
It neither assumes a globally polynomial received word nor a valid witness.
The matrix/encoder source instantiation and Rust polynomial-kernel refinement
remain separate obligations.

Both focused Lean leaves passed using only `propext`, `Classical.choice`
and `Quot.sound`; no sorry or new axioms. Commands, time/RSS/swap and logs
are in [the evidence manifest](gao-recovery-evidence.json).

The optimized Rust decoder gained cfg-only determinant, degree, evaluation
and strict-descent audits. They pass 85,482 cases exhaustive **within the
declared small coefficient/error alphabets**, not over CM31 or all strategies.
The same audits pass on the prior genuine-payment/noncanonical-C1 fixture,
which returns a checked witness. Its 45.56-second process includes extraction
and diagnostic work; it is not the four-second proving benchmark.

The missing implication is still that the intended actual accepting verifier
supplies this specified, resource-bounded extractor with sufficiently close,
authenticated C1 samples and the selected payment constraints. Actual oracle
access, replay/fuel/failure accounting, semantic/ownership validation, FS,
full-view ZK and CU parity are not consequences of decoder completeness.
