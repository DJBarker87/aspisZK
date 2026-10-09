# R648 TwoSwap sparse kernel

This is a focused field/table-model milestone. It establishes exact TwoSwap
sparse-coin preservation for two existing 13-direction families. It does not
establish universal joint target coverage, native verifier execution, privacy,
probability, or soundness.

## What compiled

| Target | Final run | Result | Wall / peak RSS / swap | Theorems |
|---|---:|---|---|---|
| `AspisV8R19/R645TwoSwapHighDirections.lean` | `1791110939556601000` | exit 0 | 0:00.90 / 2,323,836 KiB / 0 | Four TwoSwap route, transport, balance, and `SourceCircleBoundary` sparse-coin-zero facts. |
| `AspisV8R19/R647TwoSwapStructuredMoment.lean` | `1791111042226234000` | exit 0 | 0:00.89 / 2,322,160 KiB / 0 | Arbitrary-weight sparse pairing zero and structured moment zero, retaining point-1 and point-2 hypotheses. |
| `AspisV8R19/R648AugmentedTwoSwapKernel.lean` | `1791111277391648000` | exit 0 | 0:01.01 / 2,331,268 KiB / 0 | Exact `AugmentedQuotient` selected 13-family sparse-coin zero under explicit `ht` and `noneOne`, plus definitional equality of the TwoSwap source mask and R645 mask. |

All three targets used the pinned cached Lean 4.32 workspace with `-j1 -M4500`,
`MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, and `TasksMax=128`.
Every final `#print axioms` report contains only `propext`, `Classical.choice`,
and `Quot.sound`; the complete output is archived under the evidence paths.

## Exact proved boundary

R645 defines the actual TwoSwap field/table route
`TwoSwapSourceTable.order (TwoSwapSourceG.coinIndex i)`, rather than reusing
the unrelated T163 permutation. Its `actualMask` is the inverse transport of
the existing source chord code. It proves its code value, transport result and
inactive balance, and proves zero at every TwoSwap sparse coin for each
`SourceCircleBoundary.column t alpha j`, including arbitrary repeated `t`,
`alpha`, and chord inputs.

R647 applies R561's exact TwoSwap sparse scatter pairing to those zeroes. It
then uses R562 to derive the structured channel moment while retaining the two
point-functional conditions at points 1 and 2 as explicit hypotheses. Its
mask, balance, and quotient-image-tail conditions are supplied by the R645
construction.

R648 treats the separate residual-column family exactly. For
`AugmentedQuotient.quotient t ht noneOne alpha (TwoSwapWitness.degree j)
(TwoSwapWitness.slot j)`, it proves degree at most 30 for every selected `j`,
then flattened coefficients vanish from raw index 124. `sourceChord_support`
with `n=62` gives zero at every raw sparse index `128+3*i`; R645 transfers that
to the actual TwoSwap sparse coin. `ht` and `noneOne` remain assumptions.

## Not proved

This does not show that either 13-direction family covers every same-public
C1/H1/G target, nor that the two families coincide or solve the residual
matrix target. It does not derive actual q22 injectivity or `noneOne`, bind the
field/table definitions to Rust writes, prove callback/oracle behavior, or
provide a simulator, losses, privacy, or soundness conclusion.

The first remaining obligations are universal same-public joint target
coverage and the retained point-1/point-2 conditions, followed by actual
constructor/callback/oracle and soundness work.

## Evidence

The complete saved package is
[`evidence/r648-two-swap-sparse-kernel/`](evidence/r648-two-swap-sparse-kernel/).
It contains every focused source snapshot, log, receipt, direct and manual
source/cache pin, failed attempt, final axiom report, and checksum manifest.
No check was replayed for this package. It is not promoted, staged, committed,
or pushed.
