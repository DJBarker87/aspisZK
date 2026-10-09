# Selected fixed-factor regular support tail

Status: kernel-checked. `experiments/SelectedHigherYRegularTail.lean`
compiled successfully as a focused cached leaf on the capped NUC runner.
All six `#print axioms` commands report only `propext`,
`Classical.choice`, and `Quot.sound`; there is no `sorry` or new axiom.

## Exact selected event

`originalSupport c1 c2 d gamma Q` is the literal stored-symbol equality set
between

```
exactInitialEncoder ((atGamma d gamma).original Q)
NearGammaSelectedC1.rawBatch c1 c2 gamma
```

`supportGammas ... M` filters the existing
`SelectedHigherYBranch.regularGammas c1 c2 d F r Gamma` by the existence of
a **same** `Q` satisfying both `Qualified c1 c2 d F gamma Q` and
`M ≤ (originalSupport ... Q).card`. Thus the factor root, image equations,
literal quotient-family membership, original reconstruction and support
all concern one actual quotient. An unrelated convenient original or
support set cannot satisfy this interface.

`support_tail_count` proves the proposed source-shaped endpoint:

```
(M - 1024) * (supportGammas c1 c2 d F r Gamma M).card
  ≤ 1048576 * HigherYRegularBranch.budget F
```

The budget is the existing literal V7 fixed-branch budget, equivalently
`28 + 2047 * (trivariateYZWeight 28 F - 28)`. The threshold `M` and finite
challenge universe `Gamma` are arbitrary; subtraction is natural-number
subtraction, so thresholds at most 1024 give the expected trivial bound.

## Derived interfaces and retained prerequisites

The theorem takes the actual fixed received/OOD prefix, `d.Checked`, the
two circle equations and west-point exclusions, a factor in
`curvePrimeFactors (SelectedFactorCoherence.parent c1 c2)`, degree at least
three, `Retained` for the two actual OOD answer curves, and a fixed row `r`.

- Primality is derived from membership in the actual selected parent
  family and its already-proved nonzero interpolant. It is not supplied
  as an independent factor certificate.
- The selected row identity is projected from the actual `Retained`
  predicate; degree at most 28 is obtained from the real `answerCurve`.
  Factor-family membership alone does **not** imply retention.
- The candidate supplied to `regular_branch_count` is precisely
  `(atGamma d gamma).original Q`. Its factor root comes from `Qualified`;
  its actual OOD value comes from `qualified_points`.
- The support is the displayed literal equality set. The only convention
  conversion is the existing `raw_batch_eq_curve`, which commutes scalar
  multiplication to match V7's width-29 curve convention.
- Nonzero specialized derivative is extracted from `regularGammas`, not
  imposed after selecting a favorable candidate. The direct theorem then
  derives its local monic branch, Hensel and interpolation interfaces.

The proof chooses a witness separately for each gamma in the existential
event, solely to invoke the deterministic incidence theorem. No candidate
strategy or gamma-polynomial message is assumed. This does not require the
prover to fix its quotient/final before gamma or alpha: every actual later
choice satisfying the event already witnesses membership. The separate
green `SelectedOriginalInjectivity.regular_qualified_unique` can identify
those choices for the later joint query argument, but this cardinality
adapter does not need to assume or reprove that uniqueness.

## Literal threshold

`qualified_support_38230` derives the support floor from the existing
literal-family-to-original proof, including its loss of at most two
**symbols**, not two entire fibres. Therefore `supportGammas_38230` proves
that the threshold filter equals the full existing regular-gamma set.
`regular_gammas_count` concludes, with no additional support premise:

```
37206 * (regularGammas c1 c2 d F r Gamma).card
  ≤ 1048576 * HigherYRegularBranch.budget F
```

This is a fixed-factor cardinality result, not a global acceptance or
sampler bound. Singular rows, outside-family events, other factors,
actual-prefix classification, uniform challenge laws and joint
gamma/alpha/query accounting remain separate. In particular it does not
multiply gamma and query marginal bounds or charge later repairs per factor.

## Source pins

Working parent: `e969d9fa5378dd1e548c8b64b79a9e76a2270d66`.
The underlying V7 reuse remains pinned to
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5` through the existing direct
incidence leaf. No additional native dependency or build was requested.

| Source | SHA-256 |
| --- | --- |
| New `SelectedHigherYRegularTail.lean` | `669ddb612473a5df4f3a2fcf3e612939e60e589f7bb8c801e01b089ffa2fa9c1` |
| `HigherYRegularBranch.lean` | `c00114b0e29817f1c617e7b4938dca322e3ec2fdaca7cb135ca387f645623cf2` |
| `SelectedHigherYBranch.lean` | `a933e50a7cde61e00d8c68770d9200cea8656c9d3736edb26fc781ee4c998084` |
| `CoveredOriginalSymbols.lean` | `446e4337224c6cc042ed13a09d7d42fcb482c89e4d45513ba7c8c036146ef5c7` |
| `FactorIdentityCover.lean` | `8a644896ba85fc515bafc9297664494f840aa91e1904c92da5a836d4681bde4d` |

## Focused verification

The first focused attempt was green. It exited 0 in 4.11 seconds with peak
RSS 6,826,588 KiB and zero swaps under MemoryHigh 8 GiB,
MemoryMax 10 GiB, MemorySwapMax 0, CPUQuota 200%, Lean 4.32.0 and
`-j1 -M9500`. Both 911-entry provenance checks passed; no dependency or
unchanged package-wide proof suite was replayed.

```sh
bash /home/dombarker/project-offloads/aspis-higher-y.fMoMeX/run_higher_y_nuc.sh \
  /home/dombarker/project-offloads/aspis-higher-y.fMoMeX \
  SelectedHigherYRegularTail selected-higher-y-regular-tail-nuc-v1
```

- Source SHA256:
  `669ddb612473a5df4f3e612939e60e589f7bb8c801e01b089ffa2fa9c1`.
- Olean SHA256:
  `e8c25c2e0c9b3ceb6734275aa52a4ac75b5ac53275d3039d7473fe5a54415d21`.
- Manifest SHA256:
  `66165bbc464b8c961c6a988f95969ebbc2cf007a2812bff9345228566d216491`.
- Log SHA256:
  `87f537f5fbd340978680707f149992babffa3fc5f60457386541c8512fab5a49`.

This is a deterministic selected-event cardinality theorem, not an
acceptance, sampler, Fiat--Shamir, extraction, or global probability theorem.
