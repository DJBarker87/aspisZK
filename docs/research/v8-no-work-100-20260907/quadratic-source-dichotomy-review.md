# Quadratic source-factor alternative

Parent: `2c63df5aab97b826d652b2536fa269bc250386d3`.
Status: Lean-checked; three standard-only axiom audits. No numerical error is booked.

The proved `QuadraticSourceDichotomy.fixed_source_alternative` joins the
constructed parity theorem to the literal V7 trivariate factor maps. For a
fixed irreducible factor F of outer Y degree two, in characteristic other
than two, with discriminant X degree below the characteristic, it returns:

- A fixed nonzero E(X), of degree at most the discriminant X degree, such
  that both actual `FactorCoherence.pointSubstitution` root identities
  force roots of E at the two OOD points; OR
- Every finite set of gamma values admitting an actual
  `challengeCandidateHom gamma U F = 0` has cardinality at most
  `8 * trivariateYZWeight curveDegree F`.

F and this alternative are fixed before either points or gamma are
quantified. In the second branch U is existential separately for each
gamma: it may depend on alpha as well. There is no assumed fixed candidate,
candidate family membership, exact received word or successful extractor.
The helper's degree two and the full batching weight at curveDegree 28
are not identified with each other.

The source theorem derives discriminant nonvanishing from irreducibility
through the fraction field. It constructs H,R, handles the constant-X
parity branch via the checked twist obstruction, and converts the other
branch's `4*degZ(D)` count using `degZ(D) <= 2*weight(F)`.

## Still required

This is an algebraic source-map bridge, not translated Rust acceptance.
The actual selected factor family must be fixed at the legal prefix;
factor budget, discriminant X-degree/characteristic applicability, actual
two-OOD identities and conditional challenge laws must be instantiated.
The two alternatives must be charged using that causal partition, not by
conditioning on successful OOD tests and reusing an unconditional law.

Higher-Y-degree factors (at least three), accepted executions yielding no
such factor/root, the payment extractor and its resources, authentication,
full-view privacy and the Fiat–Shamir lift remain separate obligations.
No complete 100-bit subtotal follows yet. Proof-body maximum remains
40,282 bytes; this work changes no verifier operations or wire fields.

## Evidence

The predecessor source bridge `QuadraticFactorSource` and constant-case
bridge `QuadraticConstantParity` are checked separately. The combined leaf
passed the focused NUC run (Tailscale) with exit 0, wall 3.19s, peak RSS
6,843,192 KiB and zero swaps. All three audits list only `propext`,
`Classical.choice`, `Quot.sound`. A harmless unused-section-variable warning
is retained; it does not weaken the endpoint's hypotheses.

Command: `bash run_higher_y_nuc.sh <scope> QuadraticSourceDichotomy quadratic-source-dichotomy-nuc-v2`.
The runner uses Lean `-j1 -M9500`, MemoryHigh 8 GiB, MemoryMax 10 GiB,
MemorySwapMax 0 and CPUQuota 200%. Import provenance passed before/after.
Source SHA256: `7a664b39817c70cb87e503db6274e595c11c90b019395dc6783dacba3f1d8d8d`.
Olean SHA256: `e630cd21b53783741a8144afe6509a0fe12d251b66e4a85dbf133a8a41f1c231`.

Attempt v1 failed on one exposed RingEquiv-to-RingHom wrapper equality
(3.13s, 6,808,512 KiB, zero swaps). An explicit `rfl` after the small
coefficient simplification fixed that goal; no statement, cap, dependency
or mathematical premise changed. Both attempts' source snapshots, logs
and manifests are retained. Failed-attempt audit output is not green credit.

The inherited runner/cache pin is `289d7356`, independently of this source
parent; no historical log is relabelled. This is a kernel-checked identity
over the maintained source-shaped polynomial maps, not an Aeneas translation
of the Rust verifier.

## Decisive next leaf: selected family applicability

A read-only source audit identifies the pre-OOD family as
`curvePrimeFactors (SelectedFactorCoherence.parent c1 c2)`, optionally
filtered by degree Y equal to two. Do not use the OOD-dependent `Retained`
filter as though it were fixed before OOD. `SelectedOODGate.fixedInterpolant`
depends on `received29(c1,c2)` alone. This fixes the full family after C2,
before the first OOD point, not before lambda/chi.

The next focused lemma is `degX(discriminant F) <= 2*degX(F)`, using
V7 `reorderFactorCoefficients_coeff_natDegree_le` on the three actual
coefficients. `curvePrimeFactor_xNatDegree_le` and the selected parent
bound then yield `degX(D) <= 229374 < 2147483647`. These steps are identified,
not yet compiled as a selected instantiation.

For subsequent finite-family composition, existing
`FactorIdentityCover.all_factor_weights_le 28` and
`trivariateYZWeight_curveTrivariatePolynomial_lt` bound the total factor
weight by 117077. This suggests a gamma numerator of 936616 without a
factor-count multiplier, still pending an actual family/causal theorem.
`MonicFactorOOD.all_factor_x_degrees_le` and
`SelectedMonicCover.parent_x_degree` give total X degree 114687. The
current exported E-degree bound would yield the looser product degree
229374; retaining the proved intermediate `E.degree <= H.degree` and
`2*H.degree <= D.degree` could avoid that factor of two. Neither proposed
composition is an achieved probability bound or permission to sum old
overlapping ledgers.
