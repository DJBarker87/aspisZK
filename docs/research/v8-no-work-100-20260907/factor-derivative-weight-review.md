# Factor derivative weight

Parent: `e969d9fa5378dd1e548c8b64b79a9e76a2270d66`.
Status: `FactorDerivativeWeight.lean` is kernel-checked on the capped NUC
runner. Its three audits contain only `propext`, `Classical.choice`, and
`Quot.sound`; there is no `sorry` or new axiom.

The smallest endpoint needs **no positive-degree or nonzero-derivative
hypothesis**:

    degree(derivativeCurve F t A) <= trivariateYZWeight c F - c
        whenever degree(A) <= c.

Subtraction is natural/truncated. This handles F=0, Y-constant F, c=0,
and derivatives annihilated by finite characteristic. Nonzeroness remains
necessary for a subsequent root-count theorem; it is not inferred here.

## Off-by-one and hypothesis checks

- `F=ZY` has weight c+1 and derivative Z. The proposed bound is tight;
  dropping an extra one gives degree1<=0 and is false.
- The answer-degree hypothesis is necessary. For c=1, F=Y², and A=Z² in
  characteristic not2, the derivative substitution has degree2, exceeding
  weight(F)-c=1.
- Replacing truncated subtraction by `degree(D)+c<=weight(F)` without an
  extra hypothesis is false for F=1 and c=28: D=0 has natural degree0.
- No characteristic-zero assumption is appropriate. For F=Y^p in
  characteristic p, the derivative is zero; the inequality still holds.
- Tightness can coexist with a prime higher-Y factor and an actual answer
  identity: F=Y³-Z^84-X is irreducible (linear in X), and at t=0, A=Z²⁸
  gives D=3Z^56 in characteristic different from3. Its weight is84, and
  the bound56 is attained.

These are symbolic falsification checks, not executable or Lean release
claims. They identify why the draft uses a weak inequality, exactly c,
natural subtraction, and the actual answer-degree hypothesis.

## Reused proof path

The leaf imports only the already checked `FactorIdentityCover`.
`derivative_weight_le` works over any coefficient integral domain R, so
R=K[X] is available without making X carry any weight. It combines:

1. `Polynomial.of_mem_support_derivative`: a surviving coefficient i comes
   from the original coefficient i+1;
2. `Polynomial.coeff_derivative`, `natDegree_mul_le`, and
   `natDegree_natCast`: its inner degree does not increase;
3. `coeff_weight_le_localBivariateWeight` and
   `localBivariateWeight_le_of_coeff`: remove exactly the extra weight c.

The second theorem invokes existing
`FactorIdentityCover.point_degree_le_weight` on F.derivative, then the new
weight inequality. The third theorem instantiates c=28. No full resultant,
prime-factor normalization, domain enumeration, source-support assumption,
Hensel root, candidate curve or all-factor counting is introduced.

The source uses only symbolic coefficient/support reasoning and linear
natural arithmetic after expanding `(i+1)*c`; no generated numerals or
recurrences are reduced.

## Focused verification

The first focused attempt was green; no predecessor failure or broad replay
was needed. It exited0 in4.26s with peak RSS6,790,152KiB and zero swaps,
under MemoryHigh8GiB/MemoryMax10GiB/SwapMax0/CPU200%, Lean4.32.0,
`-j1 -M9500`. Both 903-entry provenance checks passed.

```sh
bash /home/dombarker/project-offloads/aspis-higher-y.fMoMeX/run_higher_y_nuc.sh \
  /home/dombarker/project-offloads/aspis-higher-y.fMoMeX \
  FactorDerivativeWeight factor-derivative-weight-nuc-v1
```

- Source SHA256:
  `68ea0c3d4986c159c02eeb314b0fff830c9b79611b9d39d35b0e89f9cf6f6c08`.
- Olean SHA256:
  `54f52f7dd1ed9a7f0b8086dffb902ef08135a0392c41c1a9b41506363465c886`.
- Manifest SHA256:
  `348b3d28578c890f28e01048894b4f91e49a37c8bcb91bbab6db48e3ceb5ec68`.
- Log SHA256:
  `40cdd191bcc196146c2867f0b8b00f4003c01333de6a41b1f265be0e060d7453`.

This closes the weighted-degree input for the proposed singular-row root
count. It does not construct the pre-OOD resultant coefficient obstruction,
prove the derivative nonzero at an actual row, or charge the exceptional
two-point OOD event.
