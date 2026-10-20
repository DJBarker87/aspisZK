# S4 v6 inner-term bound checkpoint

This packet proves that successful execution of the explicitly emitted v6 term-body extracts all eight literal limb updates, constructs the corresponding successful old `InnerLoop`, and applies the retained linear-bound theorem. The public endpoint `new_term_body_success_linear_bound` has no segment-success or old-loop-success input: it gets those facts from the full v6 body result. It derives parser and coefficient canonicality from the successful body operations and the caller-supplied coordinate bounds for `g`.

The remaining caller inputs are the prior sums envelope, `g` coordinate bounds, and explicit parser/`wideToLimbs` operation equalities. The enclosing term loop and outer batch composition remain open. This packet is a proof checkpoint, not a production-source adoption claim.

Lean 4.32, focused `-j1 -M4400` checks, and standard-only `#print axioms` results are recorded in `receipts/`. Full source/object import pins are in `manifest.json`. No `.olean` binaries are included.
