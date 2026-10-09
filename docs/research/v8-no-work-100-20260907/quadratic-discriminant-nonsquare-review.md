# Irreducibility supplies quadratic nonsquareness

`QuadraticDiscriminantNonsquare.lean` is kernel-checked. It replaces a
supplied discriminant-nonsquare premise with the literal hypotheses that
the polynomial is irreducible and has degree two over a field of
characteristic other than two. This is an algebraic ingredient, not a
classification of every selected factor or an extraction/probability result.

## Exact statements

The [new leaf](experiments/QuadraticDiscriminantNonsquare.lean) proves:

- `quadratic_shape`: from `F.natDegree = 2`, constructs the actual
  `C(F.coeff 2)*Y^2 + C(F.coeff 1)*Y + C(F.coeff 0)` representation.
- `discriminant_nonsquare`: irreducibility and that degree force
  `¬ IsSquare (discrim (F.coeff 2) (F.coeff 1) (F.coeff 0))`.
- `twist_nonsquare`: if nonsquare `D = d*H^2`, then `H ≠ 0` and `d`
  is nonsquare. No separate nonzero-H hypothesis is needed.
- `irreducible_twist_nonsquare`: the same conclusion when `d` lives in
  a smaller field and is embedded by an explicit ring homomorphism.
- `fraction_discriminant_nonsquare`: over a GCD domain, irreducibility
  and degree two derive primitivity, then Gauss's lemma gives the
  fraction-field nonsquare statement for the mapped literal discriminant.
- `fraction_twist_nonsquare`: transports a coefficient-ring decomposition
  by the literal algebra map and derives `H ≠ 0` and nonsquareness of the
  mapped `d`.

The proof uses the pinned Mathlib quadratic formula to construct a root
from a square discriminant and contradicts
`Irreducible.not_isRoot_of_natDegree_ne_one`. It does not assume roots
absent, monicity, primitivity, or the desired nonsquare conclusion.
Only a three-term symbolic coefficient expansion is evaluated.

## Applicability boundary

The generic base ring may be the actual nested polynomial coefficient
ring, with its fraction field. To use the smaller-field theorem for
`K(Z) → K(X,Z)`, the caller must still give the correct field homomorphism
and actual variable order; no implicit X/Z interchange is claimed.
The decomposition `D = d*H^2` must also be established from the factor.
This leaf does not construct the squarefree/parity decomposition or
prove its coefficient degree bounds. It can remove the nonsquare
prerequisite in the [checked twist obstruction](quadratic-twist-obstruction-review.md)
once those source identities are supplied.

No gamma-dependent chosen candidate is fixed early, no degree-two helper
bound replaces the degree-28 claim error, and no change is made to the
alpha-adaptive final interface. No numerical security claim follows
from this leaf alone.

## Focused evidence

The source was developed after research checkpoint
`9bc0ceee` and checked in the unchanged higher-Y cached overlay with
research pin `289d7356c78a4cd493fe61a54f9548f2a0c11298` and borrowed V7 pin
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`. These are distinct provenance
roles; the old overlay was not relabeled as a new checkout.

The first and only attempt,
[quadratic-discriminant-nonsquare-nuc-v1.log](experiments/quadratic-discriminant-nonsquare-nuc-v1.log),
terminated with Lean exit 0 and successful postflight: 1.35 seconds,
2,387,584 KiB peak RSS, zero swaps, six standard-only axiom audits
(`propext`, `Classical.choice`, `Quot.sound`, with a subset for the
elementary twist lemma). One harmless unused `eval_pow` simp argument
warning is retained; no replay was run to remove it.

The NUC was reached only through Tailscale `100.108.41.90`; `nuc.local`
was solely the pinned SSH host-key alias. The focused runner used
MemoryHigh 8 GiB, MemoryMax 10 GiB, SwapMax 0, CPU quota 200%, and Lean
`-j1 -M9500`. Source limits remained maxRecDepth 200 and 150,000
heartbeats. All 813 overlay provenance records matched before/after.

- Source and exact attempt snapshot:
  `445be0bb02705b28f4af6065c10803ce507b35919a1a2256ec703272e1588684`.
- Green olean:
  `7371becff4da0223587627e27b1ebc0b9d2908acc57942111fa5715299b8b750`.
- Per-run manifest:
  `241a632511b35a8008441d3e7fe741495142ef304f64c9737a847cbce3fa31ba`.
- Runner:
  `5780e61b4d286905ab912bb6ab8e103a20908f78c11bea415db40a5fad110e52`.

The source, attempt snapshot, log, manifest and compiled output are
retained under `experiments/`. Earlier checked rigidity and twist leaves
were not edited or replayed.
