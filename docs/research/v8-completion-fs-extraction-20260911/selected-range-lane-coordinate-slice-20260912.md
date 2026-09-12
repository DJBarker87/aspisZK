# Selected range-lane coordinate restriction

Status: **exact degree-three source slice proved; chronological suffix sum
still open**.

`lean/SelectedRangeLaneCoordinateSlice.lean` models the literal range lane as

```text
(eq_1008 + eq_1010 + eq_1012) * (opening^2 - opening)
```

for an arbitrary fixed trace-column table.  It proves that restricting any
one challenge coordinate leaves both the three-row selector and the table MLE
linear, so their composed residual has degree at most three and therefore
meets the selected degree-27 bound.  Evaluation of the restriction is proved
equal to the same literal source expression, including the exact selected row
numbers.

This does not infer an off-domain value from the Boolean table and does not
take a `SourcePolynomial` or endpoint equality as a premise.  The remaining
constructor seam is to sum these slices over every Boolean future suffix and
prove the initial and adjacent-round partitions.  The other 93 semantic
outputs and literal Rust machine refinement also remain open.

## Focused evidence

- Target source SHA-256:
  `6e5a373578722dd8ee969987f7c0e0cc35fb756e585ae567b6d5b4366a099ea9`.
- NUC/Tailscale compile: exit 0, 3.62 seconds wall time, 6,668,156 KiB
  peak RSS, zero swap, with `MemoryHigh=9G`, `MemoryMax=10G` and
  `MemorySwapMax=0`.
- Artifact SHA-256:
  `ebcd24d8406f3bf87b9cbe3cf9aaba72e23603c6968c60977d43403734a2e395`.
- Printed axioms are only `propext`, `Classical.choice` and `Quot.sound`.

The exact command, environment and per-declaration scope are recorded in
`results/v8-completion-fs-extraction-20260911/selected-range-lane-coordinate-slice-v1/report.json`.
No protocol bytes, verifier checks, or probability ledger changed.
