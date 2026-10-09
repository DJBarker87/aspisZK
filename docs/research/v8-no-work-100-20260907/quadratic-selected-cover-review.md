# Selected fixed quadratic family: checked cover

Source parent: `be7a1731bd4d71de50fa39767a53523bf0bc9ff0`.

`SelectedQuadraticCover.fixed_cover` is Lean-checked. For the actual
arbitrary received C1/C2 pair, it constructs E and a finite set B such that:

- E is nonzero and has degree at most 114687.
- B has at most 936616 field elements.
- If one quadratic prime factor of the fixed selected parent has both
  actual OOD polynomial identities and an actual candidate root at gamma,
  then both OOD points are roots of E, or gamma belongs to B.

E and B are selected from C1/C2 before quantification over either OOD
point, either polynomial answer, gamma, or the polynomial candidate U.
The SAME factor must satisfy both identities and the root equation. U
may be chosen after gamma and alpha. It is not retrospectively frozen.

The family is the degree-Y-two filter of
`curvePrimeFactors (SelectedFactorCoherence.parent c1 c2)`, not the
OOD-dependent `Retained` subfamily. Its fixing boundary is after adaptive
C2 and before OOD. This does not move C2 or the resulting tuple before
lambda/chi, nor prove early-C1 semantic binding.

## What is newly discharged

The exact selected degree leaf proves `degX(D) <= 229374 < 2147483647`
for every actual factor. Characteristic is derived through the faithful
M31-to-QM31 algebra map. The sharp source theorem preserves
`2*deg(E_F) <= degX(D_F) <= 2*degX(F)`.

`QuadraticFamilyAssembly.assemble` constructs a product of the fixed
obstruction polynomials and a union of the fixed exceptional-gamma sets.
The budget is additive over the multiset, including repeated factors:

    degree(E) <= sum degX(F) <= 114687
    card(B) <= 8 * sum YZWeight28(F) <= 8 * 117077 = 936616.

No factor-count multiplier, OOD-conditioned family or chosen-candidate
membership premise supplies the improvement. The degree-28 claim curve
is retained throughout; the degree-two helper is not substituted for it.
Existing V7 factor-weight, coefficient-degree and parent-degree theorems
are reused through the pinned imported source/output closure.

## Exact remaining event

This is a deterministic cover of the actual quadratic factor-root class,
not complete verifier acceptance. A fresh uniform nonzero gamma law at
the legal prefix would charge B by at most `936616/(|K|-1)`. That ideal
law and the sequential OOD sampler bound for the constructed E still
need to be composed against the actual game. No numerical global subtotal
is claimed, and neither alternative is silently conditioned away.

The existing `SelectedIdentityCover` supplies factor roots only under its
actual literal-family/image and checked-point prerequisites. This theorem
does not discharge those prerequisites for all accepted arbitrary-oracle
executions. In particular, higher-Y-degree factors (at least three),
remaining linear classifications, source/replay/provider failures and
the checked bounded-resource payment extractor remain explicit obligations.
Authentication, FS resources and full-view privacy remain separate gates.

The mathematical construction of B uses a finite field universe with an
existential polynomial-root predicate. Lean proves its cardinality
symbolically; no QM31 universe was enumerated. This is NOT a practical
extractor algorithm or a source of new verifier data.

## Focused runs and scope

All runs use the inherited NUC workspace over Tailscale, runner parent
`289d7356`, pinned V7 source `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`,
MemoryHigh8GiB/MemoryMax10GiB/SwapMax0, Lean `-j1 -M9500`.

`QuadraticFamilyAssembly` v2: exit0, 2.90s, RSS6,836,504KiB, zero swaps,
one standard-only audit. v1 failed on missing explicit arguments to the
finite-union cardinality lemma (2.83s, RSS6,803,796KiB); its source and log
are retained. No theorem or cap changed.

`SelectedQuadraticCover` v2: exit0, 3.41s, RSS6,872,512KiB, zero swaps,
two standard-only audits. v1 failed on small Multiset API arguments and
untyped point/answer binders (3.07s, RSS6,829,764KiB); its source and log
are retained. Both generic and selected steps used only symbolic algebra.

Commands, with the recorded scope substituted:

    bash run_higher_y_nuc.sh <scope> QuadraticFamilyAssembly quadratic-family-assembly-nuc-v2
    bash run_higher_y_nuc.sh <scope> SelectedQuadraticCover selected-quadratic-cover-nuc-v2

Selected source SHA256:
`e4d3b6b14119b2116cd770bf4c24a745e614a640e910a33e454d16b70ad912b9`.
Selected olean SHA256:
`a1cd989840bc710d3502dee1986c555140d3167c32e67723a78b93859230068e`.
Assembly source SHA256:
`8d6161fe6ce9772d1dc5b6132c118f1016091adff49b9ed97ae85d7a4f06363e`.
Assembly olean SHA256:
`8259fa82a84a1bdf399c6c6741026f0fa3a4f5d690ad52bc7937920ae0877b83`.

No production, protocol, transcript, wire or runtime change. Maximum body
remains 40,282 bytes, grinding credit zero. These are Lean measurements,
not CU, prover time or extraction-time measurements.

## Next decisive task

Compose this fixed family cover with the existing causal OOD/gamma game
and selected factor classification, preserving all branches. This should
replace the degree-two part of the previous higher-Y obligation by named
OOD and gamma events; it must not charge their overlap twice. Then address
the still-uncovered degree-at-least-three factor class, rather than
re-proving quadratic counting identities.
