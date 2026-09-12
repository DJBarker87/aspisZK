# Selected range-lane coordinate restriction

Status: **exact degree-three source slice and chronological suffix-sum source
constructed**.

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
take a `SourcePolynomial` or endpoint equality as a premise.

`lean/SelectedRangeLaneSourcePolynomial.lean` then sums these exact slices
over every Boolean future suffix, proves the head/tail partition at every
adjacent round, proves the initial Boolean-cube sum, and packages the result as
a chronological degree-three `SourcePolynomial`. The trace-column table is an
explicit input fixed before the challenges. Its initial table is connected to
the selected big-endian Boolean row decoder using the existing injectivity
theorem and equal finite cardinalities. The other 93 semantic outputs and
literal Rust machine refinement remain open.

## Focused evidence

- Coordinate source SHA-256:
  `b22d00da11ff279db60a420371b9f20f34127dadb1f5d92123e52a1bed6cbfe2`.
- Coordinate NUC/Tailscale compile: exit 0, 4.95 seconds wall time,
  6,615,036 KiB
  peak RSS, zero swap, with `MemoryHigh=9G`, `MemoryMax=10G` and
  `MemorySwapMax=0`.
- Coordinate artifact SHA-256:
  `0693a5e8e0f6d58c918654729d5e0323c526fe05e15fa167c9f4a9d20d2d19a2`.
- Source-polynomial source SHA-256:
  `65410701bc94e70f6cfbb11fafe5ed3b2147553ba69e536d36616a629dcf7b02`.
- Source-polynomial NUC/Tailscale compile: exit 0, 6.40 seconds wall time,
  6,640,964 KiB peak RSS and zero swap under the same scope limits.
- Source-polynomial artifact SHA-256:
  `c5b1ce1c52039d97ec9e61b4ee8dd76a40a4258aa0dff84b0c205c5b4147c218`.
- Printed axioms are only `propext`, `Classical.choice` and `Quot.sound`.

The exact commands, environment and per-declaration scope are recorded in the
coordinate and source-polynomial JSON reports under
`results/v8-completion-fs-extraction-20260911/`.
No protocol bytes, verifier checks, or probability ledger changed.
