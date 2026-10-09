# Fixed regular higher-Y branch: direct incidence

Status: `HigherYRegularBranch.lean` is kernel-checked on the capped NUC
runner. All 13 audits contain only `propext`, `Classical.choice`, and
`Quot.sound`; there is no `sorry` or new axiom in the retained result.
Working source parent: `e969d9fa5378dd1e548c8b64b79a9e76a2270d66`.

## Proposed exact endpoint

For one fixed prime factor `F` with Y degree at least three, one fixed OOD
point `x`, and one fixed answer polynomial `A` of degree at most 28, retain
the literal identity `pointSubstitution x A F = 0`. Let `G` be a finite
gamma set and let `candidate gamma : Fin 1024 -> QM31Exact` be arbitrary
actual original messages. For each gamma in G require:

- at least M actual support coordinates;
- exact initial-encoder equality to the fixed 29-lane received batch on
  that support;
- the GRS polynomial of this same message is a root of this same F;
- its value at x equals `A(gamma)`;
- the actual derivative curve at gamma is nonzero.

The proposed conclusion is

    (M - 1024) * G.card <= 1048576 * B_F
    B_F = fixedBranchEvaluationBudget 1024 28 F.natDegree 1 28
            (trivariateYZWeight 28 F)
        = 28 + 2047 * (trivariateYZWeight 28 F - 28).

There is no supplied component curve, formal root, local-factor registry
membership, full-resultant certificate, decoder success, or valid-witness
premise. Candidate messages may be chosen independently at every gamma.
The selected event adapter must retain the same actual quotient/original
message and actual post-alpha final when invoking this endpoint.

## Internal derivations

`MonicOODBranch` constructs the actual monic local branch `Y-A(Z)`, its
adjoined root, empty pole set, V7 power-series root, and nonzero regular
denominator. This draft additionally derives its coefficient bound and
exact weight 28, and derives `SimpleSpecializedRoot` from the literal OOD
identity, point value, and nonzero derivative evaluation.

The normalized received polynomial at coordinate i is exactly
`receivedCurvePolynomial (exactInitialNormalizedLanes lanes) i`. The draft
uses the deployed nonzero GRS multiplier to prove actual source agreement
with its evaluation; it is not an assumed normalization correspondence.

Under the negation of the proposed inequality, support cardinality gives
`M <= 1048576`, while the exact branch budget gives `G.card > W_F >= 28`.
The draft passes the strict incidence inequality directly to
`exists_ambient_curve_of_fixed_branch`, not through the old outer-selection
bound or its `28*N+1` concurrency reserve.

The ambient-to-curve adapter uses the existing generic
`ReleasedLift.exists_released_components_of_ambient_curve` on the linear
evaluation map of `SelectedGRSSubmodule.encoder`. Thus its interpolation
nodes contain actual 1024-coordinate messages and its component messages
remain in that domain. Its encoder is the proved source GRS numerator map,
not an arbitrary degree-at-most-1024 ambient polynomial space. Agreement at
the existing injective million-point grid identifies the polynomials.
This constructs a degree-at-most-28 polynomial in gamma with polynomial
X-coefficients containing every candidate on G.

`HigherYCurveObstruction.coherent_specializations_card` then bounds the
same G by W_F, contradicting the derived strict inequality. Nothing is
assumed about a candidate curve before this contradiction argument.

## Reuse and cache boundary

Borrowed V7 source pin: `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.
The pointwise source normalization is narrowed from the pinned initial-code
body of `V7ExactCorrelatedAgreementConcreteBranch`; the old large concrete
wrapper is neither imported nor replayed.

Both principal reused imports and their closure were metadata-checked in
the inherited NUC overlay, without mutation:

- FixedBranchCurve source
  `d3fa20c540ebb21ccdb29b54b1905689ca3cc381adb5823dc390b4114dddf734`;
  olean `e5aac67e2230fc4afe9f3cb496849ecdbdee537b25760440e3104d73bf188b18`.
- ReleasedLift source
  `83581c24ea8dd1ba7b36aa2d90833d68901111c20b9787a0416bd68cc3bd9612`;
  olean `3813bf8365ff5b5bc3e8e785c09fc30e2ebab76705ec9c1f4c96f32becaee538`.

## Remaining consumers and limits

The decisive next probability consumer should stratify actual whole-fibre
support m. `CoveredOriginalSymbols` supplies at least `4*m-2` original
symbols; retaining symbolic M permits using that bound, not only the
minimum `M=38230`. This draft does not itself derive a joint query tail.

Both-singular OOD rows remain outside this regular-branch endpoint. The
factor-family additive count, singular-point obstruction, acceptance
partition, gamma/query freshness, early-C1 own support, and actual checked
payment extraction are not silently discharged. No security margin or
protocol parameter is changed.

## Focused verification

The final focused command was:

```sh
bash /home/dombarker/project-offloads/aspis-higher-y.fMoMeX/run_higher_y_nuc.sh \
  /home/dombarker/project-offloads/aspis-higher-y.fMoMeX \
  HigherYRegularBranch higher-y-regular-branch-renamed-nuc-v1
```

It used Tailscale `dombarker@100.108.41.90` with the pinned host-key alias,
Lean 4.32.0, `-j1 -M9500`, MemoryHigh 8 GiB, MemoryMax 10 GiB,
MemorySwapMax 0 and CPUQuota 200%. The final exit was zero in 6.97 seconds,
with peak RSS 6,829,020 KiB and zero swaps. Both 899-entry provenance checks
passed. An unrelated capped V7 build was preserved; the declared combined
maximum remained 20 GiB.

The five failed predecessor attempts are retained rather than overwritten:

| Attempt | Exit | Wall seconds | Peak RSS KiB | Failure class |
| --- | ---: | ---: | ---: | --- |
| old-name v1 | 1 | 3.84 | 6,815,604 | monomial API arity, too-low recursion setting, tight-arrow parse |
| old-name v2 | 1 | 3.84 | 6,820,188 | tight-arrow parse |
| old-name v3 | 1 | 4.17 | 6,829,460 | too-low recursion setting and empty-set namespace |
| old-name v4 | 1 | 5.39 | 6,816,916 | too-low recursion setting |
| old-name v5 | 1 | 4.36 | 6,814,604 | too-low recursion setting |

The successful source removes the artificial local recursion cap and uses
the already compiled source normalization lemma; it does not raise the NUC
memory cap or change the theorem. The final module name also removes an
accidental duplicated `Regular` from the draft name.

- Green source SHA256:
   `c00114b0e29817f1c617e7b4938dca322e3ec2fdaca7cb135ca387f645623cf2`.
- Green olean SHA256:
  `806fb26c9a0d29cfc3da38649c203af38f78e604b7c9979f66d39e516cd6e431`.
- Green manifest SHA256:
  `5dd1718b1730f913f2d0246134b81c18e1c99a8ef55133780879c5e4d3c13434`.
- Green log SHA256:
  `9e0307be6656c1d8db00112196715d7e87f98c26f58276871e6d028c42086a7c`.
