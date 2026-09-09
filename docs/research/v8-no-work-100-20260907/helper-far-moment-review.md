# Exact reduced relation-compatible far moment

Research base: `edb199c12fcc41f00330298b95b4736f60ac6f3a`.
This continuation completes an optimized exact causal search in a **restricted
F19 model**, not a V8 soundness bound or a payment execution. It consumes the
new [relation-compatible moment reduction](relation-compatible-moment-review.md)
and preserves the earlier [frozen strategy preflight](helper-ood-strategy-review.md).

The new result is that relation-compatible far agreement remains substantial
under legal adaptive choices in this model. Setting the post-alpha prior to
zero is also not without loss of optimality for complete suffix acceptance.
Neither observation establishes failed witness extraction: the broad far
classifier and the wrong claim against a chosen early C1 are not definitions of
knowledge failure.

## Exact model and causal order

[`helper_far_moment.rs`](experiments/helper_far_moment.rs) uses F19 and the four
circle fibres represented by `(2,4), (3,7), (4,2), (7,3)`. Slots are
`(x,y), (x,-y), (-x,-y), (-x,y)`. All sixteen points are distinct, and the four
final positions `T2(x)=2*x^2-1` are distinct. The eight coefficient basis entries
are `[1,y,x,xy,T2,yT2,xT2,xyT2]`; one primal arity-four fold produces two final
coefficients using `[1,alpha,alpha^2,alpha^3]`. Its dual uses
`[1,alpha^3,alpha^2,alpha]/4`.

Two helper profiles are fixed and reported separately, never chosen after a
challenge:

- Profile 0: early C1 and all three helper received words are zero.
- Profile 1: early C1 is zero. Helper lane `ell` is supported on predetermined
  fibre `ell`, with respective values `1+y`, `x*(1+y)`, and `(1+x)*(1+y)`.
  The fourth fibre has no helper modifications.

The two possible OOD pairs are `(0,1),(0,-1)` and `(-1,0),(1,0)`, sampled
uniformly. Their literal cross-product chords are **2x** and **2y**, not
rescaled unit chords. There are no poles at the sixteen evaluation points.
Both 29-component OOD answer vectors are fixed in advance: lanes 0 and 28 are
one, and all others are zero. Lane 0 is a genuinely false claim about the fixed
zero early C1. The scalar-power claim polynomial is literally `1+X^28` before
field evaluation; this is not an assertion that all helper components already
possess polynomial interpretations. F19 evaluation has Fermat periodicity, so
these rates cannot be extrapolated to QM31.

Writing `s = gamma^-26 * (1+gamma^28)`, the normalized received quotient is

```
(H + gamma*G + gamma^2*D - s) / L.
```

Thus the received helper contribution has degree two in gamma, while the false
early claim still produces a reciprocal gamma term. It was not silently
replaced by a degree-two claim error.

| Boundary | Fixed or sampled next | Adversary's permitted choices |
| --- | --- | --- |
| Before OOD | Early C1, one helper profile, both component answer vectors | No optimization over these inputs |
| After OOD mode and fresh nonzero gamma | The received quotient and OOD interpolant | Inactive scalar, before kappa and tau |
| Fresh nonzero kappa, then nonzero tau | Shifted ordinary row weights and carried image weights | First compact response, before alpha |
| Fresh alpha in all F19 | First carried scalar and folded functional | Any of the `19^2` full final coefficient pairs |
| Fresh ordered distinct query pair | Actual final, pointwise residuals, and incoming prior | No new final or response0 choice |
| Fresh nonzero rho | `prior - rho*(r0 + rho*r1)` | Three sequential abstract degree-six repair responses |

The four ordinary row scales are `[1,kappa,kappa^2,kappa^3]`. These are three
**reduced product rows**, not the selected ten-coordinate semantic/successor
kernel. The image coordinates are `[Q7,2*Q6]` for chord 2x and `[Q7,-2*Q5]` for
chord 2y, mixed with tau and tau squared before response0. The ordinary affine
interpolant correction uses the actual constant-coefficient functional
`ordinary(kappa)[0]`, not a sum of row scales.

Response0 exhausts all `19^2` choices of c0 and c1, with c2, c3, c5, c6 fixed
to zero and c4 reconstructed as `claim/4-c0`. This is a restricted response
family, not the full six-free-coefficient first round. The remaining three
rounds retain the actual degree-six scalar boundary grammar and sequential
adaptivity, but **are abstract discrepancy rounds**: the reduced 8-to-2 vector
does not have the production dimensions for three further arity-four folds.

For each nonzero current discrepancy a polynomial proportional to
`[0,3,15,8,5,17,9]` has boundary `4*(c0+c4)=discrepancy` and exactly six roots.
The six-root upper bound and this attainable policy give the exact abstract
three-round repair probability

```
(19^3 - 13^3)/19^3 = 4662/6859.
```

The program also exhausts that policy's complete three-challenge tree for all
nineteen initial discrepancies. This is not a theorem that every actual
production terminal can realize an arbitrary discrepancy polynomial.

## Backward induction and numerical results

Every challenge and every permitted causal response is enumerated. In
particular, the response maximum is **outside** the fresh-alpha sum, the final
maximum is inside it, and the inactive maximum is outside the kappa/tau sum.
The two OOD modes and all eighteen nonzero gammas are averaged. There is no
favorable-transcript selection, Monte Carlo, or normalization by the number of
adversarial choices.

For this experiment, a final is called far when it disagrees on more than one
of the four fibres, hence has matching count M at most two. This is not the
selected 9,301-fibre radius. For a fixed final its pointwise query probability
is exactly `M*(M-1)/12`. The code also computes the minimum complete-fibre
distance to an image-valid eight-coefficient quotient, by all sixteen support
systems with the image equations: every one of the 72 fixed
profile/mode/gamma contexts has minimum distance **three**. That distance
classifier does not assert unextractability.

Each table row is independently maximized and may have a different policy:

| Objective | Profile 0 exact probability | Profile 1 exact probability |
| --- | --- | --- |
| Complete abstract suffix acceptance | `2245519525/3040128288` | `3349818995/4560192432` |
| Acceptance and far final | `2208161737/3040128288` | `238454657605/328333855104` |
| **Zero prior, far final, pointwise queries pass** | **`7219/73872` (0.09772309)** | **`21365/221616` (0.09640549)** |
| Far pointwise queries, ignoring prior | `3/19` (0.15789474) | `341/2052` (0.16617934) |
| Acceptance, far final, and zero prior before queries | `6566159255/9120384864` | `729288617/1013376096` |

The un-reduced common denominator for all objectives is
`328333855104 = 2*18*18*18*19*12*18*19^3`. Pointwise objectives pad the absent
rho/tail draws by their full cardinalities; their events do not depend on those
draws. The machine-readable result records and inactive policies are retained
in the [green log](experiments/helper-far-moment-v1.log).

Complete far acceptance exceeds its prior-zero-restricted counterpart by
`2099734416/328333855104` and `2165145697/328333855104`, respectively. Therefore
requiring prior zero is not an exact optimization-preserving simplification,
even after the earlier choices are handled causally. This does **not**
contradict the proved moment reduction: that reduction explicitly pays for
rho cancellation and later repairs rather than declaring them impossible.

The values are exhaustive optima only within the stated restricted family.
They are attainable lower bounds on the optima of less restricted versions of
this same toy game, **not upper bounds** for arbitrary helper words, the full
response grammar, or V8.

## Seven-alpha incidence is not coherent recovery

For the zero-prior far pointwise objective, every positive score is exactly
1/6: far requires M at most two and both distinct queries require M at least
two. Consequently the exact moment numerators determine **129,942** and
**128,190** qualifying `(prefix,alpha)` incidences across **11,664** prefixes
per profile, under an optimizing inactive/response policy. Each prefix has
one response fixed before alpha, but its final may vary with alpha. The means
are 11.1404321 and 10.9902263 qualifying alphas per prefix.

Let h count prefixes with at least seven qualifying alphas. A prefix outside
that class contributes at most six, and any prefix contributes at most
nineteen. Thus `total <= 6*11664 + 13*h`, giving the rigorous lower bounds
**4,613** and **4,478**. These are lower bounds, not measured exact histogram
counts. They are not counts of coherent cubic final curves or recovered
quotients. The saved search retains inactive argmax choices but not all
response/final tie choices, so it does not determine that classification.

There is a concrete reason to preserve this distinction. In profile 0 the
received word is `-s/(2x)` or `-s/(2y)`. Its folded values are respectively

```
-s*alpha^2/(2*x^2),       -s*alpha/(2*y^2).
```

Here s is nonzero for every nonzero F19 gamma: `gamma^28=gamma^10` is a
nonzero square, whereas -1 is not a square in F19. For each of the six pairs
of distinct final positions, interpolate the reciprocal values with a linear
final polynomial. Multiplying that polynomial by alpha squared or alpha gives
a coherent, cubic-or-lower final curve fitting those two fibres for all alpha.
Its corresponding quotient has only lanes 2/6 or 1/5, respectively. Its final
slope is nonzero because the reciprocal values at the two positions differ,
so its image residual `2*Q6` or `-2*Q5` is nonzero. **All six such two-fibre
curves are image-invalid.** This statement follows from the displayed exact
source formulas; no additional search or Lean replay was run to establish it.

An adaptive final can instead switch between the six curves after alpha.
Seven qualifying alphas therefore do not imply seven alphas for the same
curve or the same matching fibre pair. With six pairs, the pigeonhole
principle gives only two occurrences of some pair from seven incidences.

For a genuinely coherent fixed quotient Q, both final coordinates are cubic
polynomials in alpha, the carried dual weights are cubic, and the response is
degree at most six. Its prior is then a polynomial of degree at most six.
Seven distinct zero-prior alphas force that polynomial to vanish identically.
This useful criterion cannot be applied to independently chosen finals. It
also does not on its own separate ordinary and image errors or produce a
payment witness. The exact field/source-shaped count and the missing
coherence implication must remain separate.

The reduced game therefore makes a shared-support or coherent-curve
condition worth testing, but does not establish it. If a recovery provider
requires that condition, accepted branches where it fails need another
recovery method or a quantitatively bounded contribution. The entire far
event must not be charged as knowledge failure: some far executions can be
recoverable, and this fixture is not a valid-payment trace in the first place.

## Execution, checks, and scope

Run from the research worktree with a new log path:

```sh
bash docs/research/v8-no-work-100-20260907/experiments/run_helper_far_moment.sh \
  /absolute/path/to/a-new-helper-far-log.log
```

The runner compiles the standalone source using
`rustc --edition=2021 -O -C overflow-checks=yes`, with a 1 GiB aggregate RSS
guard and a 90 CPU-second limit. The expectation before running was 30–60 s
of search; the measured search was faster. No dependency package was built.

| Stage | Exit | Wall time | Peak RSS (bytes) | Swaps |
| --- | ---: | ---: | ---: | ---: |
| Optimized standalone compilation | 0 | 1.34 s | 140,853,248 | 0 |
| Complete restricted causal search | 0 | 9.75 s | 2,408,448 | 0 |

The 23,328 weight prefixes cover 160,006,752 adaptive final candidates,
3,040,128,288 final/prior comparisons, 160,006,752 response candidates, and
3,040,128,288 response/alpha lookups. Tables avoid materializing these billions
of states. Internal timings were 0.165 s for query histograms, 4.981 s for
final/prior values, and 4.135 s for response optimization. The source performs
9,104 independent algebra/reference checks and 20,520 direct scalar versus
histogram checks, in addition to the tail trees. These checks validate this
executable model; they are not a universal field proof or a cryptographic
probability experiment.

Rust was `1.93.0 (254b59607 2026-01-19)`. SHA256 pins:

- New source: `2e4f615b11754126bd62c5f97cf92a9802d6de03f375ab762d49dee15d081588`.
- Runner: `80f44d1e2151a242d41ee71059537193a335541ea5969cdcdd41d1dd0d316395`.
- Frozen prior source, checked unchanged by the runner:
  `322056c4ceba5ae1c18391386ade43b50695cb4ecc2a839a0eac8ad6069da9db`.

No Lean declaration or axiom audit is claimed for this Rust search. The
separate [adaptive-final prior correction](adaptive-final-prior-review.md)
is already kernel-checked and is not rerun here. No witness data, production
code, proof messages, CU measurement, or masking distribution changed. The
maximum body model remains
`697*16 + 52 + 24 + 22*621 + 2*296*26 = 40,282` bytes.

The next bounded experiment is to retain an optimizing response and its
post-alpha final choices for selected predeclared prefixes, classify common
cubic curves and shared supports, and distinguish invalid-image coherent
candidates from unrelated adaptive finals. That diagnostic was **not run** in
this continuation. A new general upper bound must charge uncovered accepted
mass and preserve extraction success; neither the toy percentages nor the
seven-alpha incidence counts supply the missing QM31 bound.
