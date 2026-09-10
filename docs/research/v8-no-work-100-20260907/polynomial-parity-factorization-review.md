# Literal polynomial parity decomposition

Status: `PolynomialParityFactorization.lean` and
`PolynomialParityLocalization.lean` are kernel-checked. Together they
construct literal polynomial parity factors, prove localized
squarefreeness and both exact degree identities. The earlier checked
nonsquare and twist leaves remain frozen.

## Smaller exact decomposition

For nonzero `D ∈ K[Z][X]`, it suffices to construct literal polynomials
`H,R` with `D = H²R`, `H ≠ 0`, `R ≠ 0`, and `Squarefree R`. There is no
need to extract an additional `a(Z)` at this stage. Odd Z-only factors
can stay in R; even Z-only multiplicities stay in H. The normalization
unit must be absorbed in R, not discarded or assumed to have a square
root.

The [generic leaf](experiments/PolynomialParityFactorization.lean) uses
the normalized factor multiset s and the formulas

`H = ∏ p∈s.toFinset, p^(s.count p / 2)` and
`R₀ = ∏ p∈s.toFinset with s.count p % 2 = 1, p`.

The symbolic identity `n = 2*(n/2) + n%2` yields `s.prod = H²R₀`.
Distinct normalized primes are relatively prime, so R₀ is squarefree.
`prod_normalizedFactors` supplies a unit u with `s.prod*u = D`;
choosing `R = R₀*u` gives exact equality and preserves squarefreeness.
Nonzero H and R follow, rather than being assumed.

The smallest focused leaf has four audits: scalar exponent parity,
multiset product parity, squarefreeness of the odd-factor product, and
existence of the literal squarefree remainder. It applies directly with
the UFD `K[Z][X]`; no rational functions are introduced into H or R.

## Exact cached APIs

The pinned Mathlib sources are:

- `RingTheory/UniqueFactorizationDomain/NormalizedFactors.lean`:
  `prod_normalizedFactors`, `irreducible_of_normalized_factor`,
  `normalizedFactors_eq_of_dvd`.
- `Algebra/BigOperators/Group/Finset/Basic.lean`:
  `Finset.prod_multiset_count`, `Finset.prod_filter`, `Finset.prod_pow`.
- `Algebra/Squarefree/Basic.lean`:
  `Finset.squarefree_prod_of_pairwise_isCoprime`, which despite its name
  takes **IsRelPrime**, not a Bezout IsCoprime premise;
  `Associated.squarefree_iff`, `Squarefree.ne_zero`.
- `RingTheory/Polynomial/GaussLemma.lean`:
  `IsPrimitive.irreducible_iff_irreducible_map_fraction_map` and
  `IsPrimitive.dvd_of_fraction_map_dvd_fraction_map`.

## Checked localization bridge

The [dependent leaf](experiments/PolynomialParityLocalization.lean)
proves squarefreeness of the remainder's image in `K(Z)[X]`. Its
`squarefree_fraction_map` applies to any squarefree polynomial over the
stated GCD/UFD base. The exact factor argument avoids a separately
primitive H:

1. A nonzero X-degree-zero factor is `C c`; its map is a unit because
   nonzero c is invertible in K(Z).
2. A positive-X-degree irreducible is primitive by
   `Irreducible.isPrimitive`; Gauss preserves its irreducibility.
3. Two distinct normalized positive-X factors cannot become associated:
   mapped divisibility descends through the primitive Gauss lemma to
   original divisibility, which forces equality of normalized factors.
4. Thus the mapped odd factors are pairwise relatively prime and each
   is a unit or irreducible; their product and the mapped unit are
   squarefree.

No claim is made that an arbitrary polynomial homomorphism preserves
squarefreeness. This argument depends specifically on fraction-field
localization and the primitive positive-degree factors.

## Degree and specialization obligations

The checked `bivariate_parity` constructs nonzero literal `D=H²R` and
then `Polynomial.natDegree_mul` and
`Polynomial.natDegree_pow` give
`degX D = 2*degX H + degX R`. Apply the actual
`Polynomial.Bivariate.swap` ring equivalence before the same argument
for `degZ D = 2*degZ H + degZ R`. Both identities are conclusions of the
checked theorem; no specialization-degree preservation is assumed.

H may vanish at a particular gamma. The already checked
`QuadraticTwistObstruction.specialization_obstruction_zero` supplies a
fixed nonzero coefficient guard once the variables are explicitly
ordered for gamma specialization. Do not assume H primitive, and do
not drop this guard. A zero R specialization is not by itself a new
content exception: the new Sylvester kernel supports a zero square
specialization, while any required fixed-size leading-degree guard
remains the responsibility of its exact consuming theorem.

If R has X degree zero, write `R=C d`. Nonsquareness of d in K(Z) is
then derived from irreducibility of the actual quadratic and the
literal discriminant identity using the checked
`QuadraticDiscriminantNonsquare` bridge, after the field/order maps are
identified. This is not a declaration that every retained higher-Y
factor is quadratic or that polynomial components have been recovered.

## Focused evidence

The only attempt was
[polynomial-parity-factorization-nuc-v1.log](experiments/polynomial-parity-factorization-nuc-v1.log):
Lean exit 0 and postflight success, 0.99 seconds, 1,799,440 KiB peak RSS,
zero swaps, four standard-only axiom audits (`propext`, `Classical.choice`,
`Quot.sound`; the scalar parity lemma uses only a subset). The unused
`Nontrivial` section-variable warning in `odd_factors_squarefree` is
retained; no replay was run merely to remove a warning.

The new source was developed after research checkpoint `9bc0ceee` and
checked in the unchanged `289d7356c78a4cd493fe61a54f9548f2a0c11298`
higher-Y overlay, borrowing V7 source pin
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`. All 819 per-run overlay
provenance entries matched before and after. NUC transport was Tailscale
only. The runner retained MemoryHigh 8 GiB / MemoryMax 10 GiB / SwapMax 0,
CPU 200%, Lean `-j1 -M9500`; source maxRecDepth 200 and 150,000
heartbeats were not raised.

- Source and exact attempt snapshot:
  `056756b59c934f71c51364f2e2b4451c9f74cd4813bdaea2699db4c419e3982a`.
- Olean:
  `ed41b209d38510252e196e34de8221bc50270a7769545446aa7f12a5890de9e1`.
- Per-run manifest:
  `36021ba9e83feb4e9dacb2ed6466f18d689525de8a5b8ec9b0754bf0dc24bd37`.

The exact source snapshot, log, manifest and compiled output are retained
under `experiments/`. No old green target was edited or replayed.

### Dependent localization evidence

`polynomial-parity-localization-nuc-v1` terminated exit 1 after 1.23
seconds, 2,380,932 KiB RSS, zero swaps. Its four generic localization
lemmas already checked, but `bivariate_parity` lacked a synthesized
normalization structure for `K[Z][X]`. The failed source/log/manifest
are retained. No theorem from that incomplete module was promoted as
checked.

The only repair was a declaration-local classical choice of the existing
`NormalizedGCDMonoid (Polynomial K[X])` in the constructive existential
theorem. This supplies a choice of normalized representatives; it adds
no hypothesis, axiom, concrete arithmetic, or resource-limit change.

[polynomial-parity-localization-nuc-v2.log](experiments/polynomial-parity-localization-nuc-v2.log)
is green: Lean exit 0, successful unchanged-provenance postflight,
1.45 seconds, 2,399,172 KiB RSS, zero swaps, all five audits standard-only.
All 825 overlay entries matched before/after. The same Tailscale-only
transport, 8/10 GiB no-swap scope, `-j1 -M9500`, depth 200 and 150,000
heartbeat limits were retained. Harmless unused section-variable warnings
in the constant-map helper are preserved without another replay.

- Failed v1 source/snapshot:
  `91a89eee1cce3c3bba6f85d5a0644229dd2f15cd9e80a32606270f1161d11914`.
- Failed v1 manifest:
  `7cd6f65954645989090780f51784623c677510ba043ef906229543edd92f7b95`.
- Green v2 source/snapshot:
  `bd09c25e31bbe4dfded29c3896a1dcb2aa54b939e0e9b01df810a6f3c672d73f`.
- Green olean:
  `b62de8740e735eeaa70861b8d40293e96c93d082c66f77cbd2d6f439ec418cf6`.
- Green v2 manifest:
  `c0f29014d46dd834ad258de476de03282517da805b340af37f5a5d979aa477fc`.

The parity pair contributes nine standard-only audits. Its endpoint is
the actual algebraic decomposition and localization/degree bridge,
not sampler-law, component-coverage, query-suppression or extraction.
