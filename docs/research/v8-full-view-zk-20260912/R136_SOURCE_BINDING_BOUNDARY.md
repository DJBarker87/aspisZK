# R136: first frozen-source binding boundary

Source base: `802abc5ce27fa1c5884a78eaca6f9aa8bec17ee0`.

This milestone records two distinct results.

First, Charon was run directly from the frozen selected R117
`relation_callback.rs` at `crate::before_ood`.  Extraction and Aeneas
translation both completed under the recorded zero-swap resource scopes.  The
generated `before_ood` body retains the exact source annotations at lines
120--125 and explicitly contains transcript creation, the profile, statement,
root, second-phase-root and point-claims absorptions, plus the two QM31 sampler
calls.

This is not yet a complete Rust execution theorem.  The generated overlay
still exposes the imported `aspis-core` transcript type, five labels and five
operational functions as external templates.  Broadly forcing all foreign bodies was
rejected because it pulled unsupported standard-library pointer operations
into Aeneas.  The next source obligation is therefore narrow: implement the
external layer from the separately source-extracted transcript primitives and
prove the exact `before_ood` result/state correspondence.

Second, `TwoSwapResidualPolynomial.assigned_eq_source_matrix` compiles.  For
an arbitrary 36-coordinate assignment and arbitrary injected query roots, it
identifies the assigned symbolic matrix with the complete
`TwoSwapResidualSource.matrix`, including the derived circle coordinates and
the source `kappa`, `alpha`, tensor and prior structured values.  Its axioms
are only `propext`, `Classical.choice`, and `Quot.sound`.

The matrix theorem is algebraic plumbing.  It does not establish that the
selected source challenges satisfy an admissible product-domain law, nor does
it prove privacy or soundness.  The selected verifier source is unchanged and
the measured endpoint remains **999,790 / 999,532 CU**.

```sh
NO_DNA=1 python3 docs/research/v8-full-view-zk-20260912/tools/check_r136_evidence.py
```
