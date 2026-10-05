# R864 single semantic-kernel preflight

Status: read-only preflight; no Lean target was compiled and no TSV value is proposed as a theorem premise.

## Fixed candidate and source identity

The R862 scanner labels its `s` values as `1..3`; the lead-selected scanner
candidate `(96,1)` is therefore the Lean direction

```lean
R738JointObservationModel.direction alphaSelected
  (⟨96, by decide⟩ : Fin 255) (⟨0, by decide⟩ : Fin 3)
```

because `qPair alpha d s = unitVector (4*d+s+1) - alpha^(s+1)*unitVector (4*d)`
and `direction` subtracts `qPair alpha 0 s`.

At `alphaSelected = 7`, this is exactly

```text
unitVector 385 - 7*unitVector 384 - unitVector 1 + 7*unitVector 0.
```

The fixed field and witness constants are the existing M31 base values:
`M = ZMod 2147483647`, `half=1073741824`, `quarter=536870912`,
`alpha=7`, `a=7`, `b=5`, `c=-5`, `kappa=5`, `tau=0`, and
`z=[1,1,2,3,4,2,2,3,0,2]`.  `R825CompleteSourceDeterminant` is the
current fixed-witness determinant consumer; the source direction definition
is in `R738JointObservationModel` lines 35--40.

## Verified finite schedule/stencil

The schedule code is `IndexSchedule.indexLoop` and the chord unit formulas
are `WeightedScatter.sourceChord_unit_even` and `_odd` (lines 184--217).
A source-only reproduction of those ten-fuel schedules gives:

```text
indexTargets(0)   = [1]
indexTargets(1)   = [0,2]
indexTargets(192) = [193]
indexTargets(193) = [192,194]
```

Consequently the union of possible source-chord output positions for this
four-unit direction is exactly

```text
{0,1,2,3,4,384,385,386,387,388}.
```

Using the two unit formulas, with `h = half`, the complete coefficient
stencil before substituting `h=1/2` is:

| code | `sourceChord half direction 7 5 (-5)` |
|---:|---:|
| 0 | `54 - 5*h` |
| 1 | `-7` |
| 2 | `35` |
| 3 | `-5` |
| 4 | `-5*h` |
| 384 | `-54 + 5*h^2` |
| 385 | `7` |
| 386 | `-35` |
| 387 | `5` |
| 388 | `5*h^2` |

Every other output is zero by `R787PairSupportZero.direction_sourceChord_zero_of_not_pairSupport`; for active rows this reduces to finite absence from this ten-position support.  The necessary active-table predicate is `R698ActiveCoreLayout.activeCode`, defined by `isInactive (order j)=false`.

The desired 271-coin intersection is exact at the source index level:
`TwoSwapSourceG.coinIndex i = 128+3*i` (`TwoSwapSourceG.lean:13`), hence
`coinIndex 86 = 386`.  No other coin index can be in the above stencil.
Thus the proposed semantic pairing has the symbolic core

```text
maskWeights271 half z 86 * (-35).
```

The requested mask singleton calculation is consistent with the literal
`reverseWeightBlocks` recursion (`MaskWeightBlocks.lean:61--65`):
`maskWeights271 half z 86 = half^6 * (3^5-3) = 15/4` at the selected
constants.  It is not presently an existing named singleton theorem; R864
would need one bounded list/index proof rather than treating the R862 TSV as
an assumption.  Then the final closed M31 identity is
`(-35)*(15/4) = -525/4 = 1610612604`.

`R561SparseGPairing.original_pairing` (and R861's fixed `finishCoins`
identity) supplies the appropriate bridge from this 271 sum to the original
source mask pairing.

## Required observation proofs and current issue

The active-row part has a clear sparse route: prove the ten literal stencil
positions are outside `activeCode`, then use the existing pair-support-zero
lemma above.  This is table-only and does not need a rank premise.

The point-row claim cannot follow merely from `sourcePointBasis` vanishing at
those ten *chord output* indices.  `R740SparsePointObservation` lines 47--64
shows the exact point observation for this direction is instead

```text
pointWeight(point,385) - 7*pointWeight(point,384)
  - (pointWeight(point,1) - 7*pointWeight(point,0)).
```

`pointWeight` is the transported source-chord transpose, so its four values
must be proved or cancelled through its finite gathers.  The generic
bit-zero facts in `R750WitnessPointSupport` and
`R752SharedWitnessPointSupport` can discharge individual source-basis leaves,
but they do not themselves rewrite the displayed `pointWeight` expression.
This is a material missing bridge for all three point rows.

Likewise, the five ordinary coefficient observations are `rowWeight` values
of `rawOrdinaryWeight` at degree 96 and degree 0 (R741/R795 route).  The
source-chord stencil gives the q-side support, but no existing theorem found
in this preflight turns it into those five zero row weights.  A proof would
need the ordinary-weight decomposition and the same point-weight/cancellation
facts; it should not be replaced by the diagnostic's zero vector.

Therefore a full theorem with `∀ row : ObservationRow, rawObservation ... =
0` is **not ready to compile from only the stated stencil**.  The semantic
pairing subtheorem is ready for a bounded source calculation; active rows are
ready once ten `activeCode` absence facts are named.  The point and ordinary
row portions require the two explicit finite-transpose/cancellation bridges
above.

## Proposed theorem split (for lead review)

1. `R864_direction_sourceChord_stencil`: fixed M31 equality to the table
above plus a support-zero theorem.  It uses only the source unit formulas,
finite schedules, and closed M31 arithmetic.
2. `R864_semantic_pairing`: use R561/R861, the singleton weight at 86, and
stencil support to prove the exact `1610612604` pairing and its nonzero
corollary.
3. Only after explicit fixed point-transpose and ordinary-row cancellation
lemmas exist, assemble the all-222 raw-observation statement.  Those lemmas
must be source-derived and must not import the R862 TSV as a premise.

This preflight makes no source-execution, legality, rank, privacy, or
security conclusion.

## Pinned sources inspected

| source | SHA-256 |
|---|---|
| `AspisV8R19/R738JointObservationModel.lean` | `6ac3f3dcae7040f92249da2364a016c434647e5ed050177675cead77defea9d7` |
| `AspisV8R17/WeightedScatter.lean` | `5a33cf1c7f5fa122bf3f2bc94ac6c2d4f51a25446f565faf8e3d6e20da413e0c` |
| `AspisV8R17/MaskWeightBlocks.lean` | `1c30ad396b2e78733b8495d3012a4305f60d86f78f5737b4c380e7a7b5def2f5` |
| `AspisV8R17/MaskWeightVector.lean` | `7704b224c77f95e370d44b42e8725c85c33080a58fa036017da8a6f75ff6d18d` |
| `AspisV8R19/TwoSwapSourceG.lean` | `4a09c5bdb945fb7d7c7b46a3c19d89d5d293973e8977337ff2e9603bb2491ee5` |
| `AspisV8R19/R750WitnessPointSupport.lean` | `cc7736c8fa2948f1a351a7b1626f5cadf88b9ff92c1e1b8db9b57ab443c17e4a` |
| `AspisV8R19/R752SharedWitnessPointSupport.lean` | `67e79e1b6ef6b65b92633aa0625deb5a87def5ccd29e8be6890db8165034ef55` |
| scratch `R773LowActiveKernel.lean` | `ad3fca704be4504c0d8c0567c8bdaf5a2cc7c14a878d79d45369613d98169f69` |
| scratch `R787PairSupportZero.lean` | `b17902d251355267290c8bb5fb7e6cff7a01d2e3a1f6844a41a7881290ba7b37` |
| `AspisV8R19/R825CompleteSourceDeterminant.lean` | `1a731499d3de7102bc5730b36d6a27a2df1d03e97c4ed879bab3089bfb4671e0` |

The R862 TSV was inspected only to confirm candidate naming alignment; it is
not used in any proposed formal premise.
