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

`lean/BooleanSuffixSourceConstructor.lean` now supplies this construction
generically from a multivariate value and exact one-coordinate polynomial
slices. It sums over every Boolean future suffix, proves the head/tail
partition at every adjacent round, proves the initial Boolean-cube sum, and
packages the result as a chronological `SourcePolynomial`.
`lean/SelectedRangeLaneSourcePolynomial.lean` instantiates it with the literal
range lane. The trace-column table is fixed before the challenges, and the
initial table is connected to the selected big-endian Boolean row decoder
using the existing injectivity theorem and equal finite cardinalities. Thus
the other 93 semantic outputs now require local slice/evaluation/degree proofs,
not bespoke ten-round boundary proofs. Literal Rust machine refinement remains
open.

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
  `dc9335b93dac7c56f6190f8c4486c4dea03f24ec45e874cda8d4074f867a50a1`.
- Generic-constructor NUC/Tailscale compile: exit 0, 6.40 seconds wall time,
  6,642,832 KiB peak RSS and zero swap under the same scope limits.
- Range instantiation NUC/Tailscale compile: exit 0, 2.69 seconds wall time,
  6,569,536 KiB peak RSS and zero swap under the same scope limits.
- Source-polynomial artifact SHA-256:
  `98106e7d0cd1c26d23e5c31d934c7beb1854498ac3028c3b809d2c9e55c1aabf`.
- Printed axioms are only `propext`, `Classical.choice` and `Quot.sound`.

The exact commands, environment and per-declaration scope are recorded in the
coordinate and source-polynomial JSON reports under
`results/v8-completion-fs-extraction-20260911/`.
No protocol bytes, verifier checks, or probability ledger changed.
