# First literal off-domain semantic source polynomial

Status: **one genuine degree-bounded source factor constructed; full callback
composition open**.

`lean/SelectedBooleanitySourcePolynomial.lean` follows the valid route left by
the Boolean-writer obstruction.  It constructs all ten chronological
partial-sum restrictions for the literal semantic Booleanity factor
`z * (z - 1)`, proves each message has degree at most 27, proves the initial
and every successor boundary, and packages them as an actual
`CausalSourcePolynomialTrace.SourcePolynomial`.

The terminal theorem reaches the same off-domain `z * (z - 1)` expression at
the sampled point.  It does not infer that value from the zero Boolean table;
indeed the separate Boolean-row theorem proves only that the restriction
vanishes on Boolean points.  This is therefore a constructive source-polynomial
instance rather than the false MLE shortcut rejected in the preceding review.

The remaining source seam is substantial: compose the real range selector,
opening polynomials, the other 93 semantic outputs, Poseidon/Copy/helper terms
and the selected masking polynomial, then refine those formulas to the pinned
Rust callback.  This leaf closes one representative source factor, not the
whole payment semantic callback.

## Focused evidence

- Base revision: `91235bb2aec48c37d8a7183f82f40040c83dbdbe`.
- Target: `SelectedBooleanitySourcePolynomial.lean`.
- Source SHA-256:
  `0454efc93af47d4be82b855da708aa545ac4502413f7cbe69ab015e6db21a99b`.
- NUC/Tailscale focused compile: exit 0, 4.69 seconds wall time,
  6,593,444 KiB peak RSS and zero swap, inside a systemd scope with
  `MemoryHigh=9G`, `MemoryMax=10G` and `MemorySwapMax=0`.
- Artifact SHA-256:
  `8d56bc2c3d243647ad132e892617f1eda83a5418da73742571aabeff26ce813a`.
- Every printed declaration uses only `propext`, `Classical.choice` and
  `Quot.sound`; there is no `sorryAx` or custom axiom.

The exact command, pinned Lean 4.32.0 provenance and per-declaration axiom
inventory are in
`results/v8-completion-fs-extraction-20260911/booleanity-source-polynomial-v1/report.json`.
No broad replay was used.

No protocol or proof bytes changed and no probability claim is made.
