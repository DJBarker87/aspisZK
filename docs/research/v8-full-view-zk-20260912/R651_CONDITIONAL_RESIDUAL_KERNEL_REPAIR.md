# R651 Conditional residual kernel repair

This milestone proves a conditional field/table-model repair for the selected
13 residual observations. It does **not** prove universal joint coverage,
privacy, security, source execution, or a probability law.

## Verified chain

| Target | Final run | Exit | Wall / peak RSS / swap | Result |
|---|---:|---:|---|---|
| R645 TwoSwap high directions | `1791110939556601000` | 0 | 0:00.90 / 2,323,836 KiB / 0 | Routes the existing chord-mask family through the actual TwoSwap sparse positions; proves code, transport, balance, and sparse-coin zeroes. |
| R647 TwoSwap structured moment | `1791111042226234000` | 0 | 0:00.89 / 2,322,160 KiB / 0 | Gives arbitrary-weight sparse pairing zero and structured moment zero, retaining point-1/point-2 hypotheses. |
| R648 Augmented TwoSwap kernel | `1791111277391648000` | 0 | 0:01.01 / 2,331,268 KiB / 0 | Gives sparse-coin zeroes for the exact selected `AugmentedQuotient` 13-family under `ht` and `noneOne`. |
| R649 TwoSwap residual repair | `1791111521097260000` | 0 | 0:01.38 / 3,291,688 KiB / 0 | Under nonzero exact source-shaped residual determinant, solves any selected 13-coordinate observation target. |
| R650 residual combination kernel | `1791111732424010000` | 0 | 0:01.84 / 3,288,772 KiB / 0 | Any R649 combination preserves all 271 sparse coin zeroes, 22-root/all-slot evaluations, and 32 first folds. |
| R651 residual kernel repair | `1791111827530788000` | 0 | 0:01.26 / 3,282,368 KiB / 0 | Combines the target repair and the three preservation properties plus inactive balance. |

All runs used the pinned cached Lean 4.32 workspace, `-j1 -M4500`,
`MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, and `TasksMax=128`.
Every final `#print axioms` report contains only `propext`,
`Classical.choice`, and `Quot.sound`. Complete reports, every saved changed
failure, logs, receipts, source snapshots, import pins, cache hashes, and
checksums are in the evidence package.

## Precise theorem boundary

`R651ResidualKernelRepair.residual_kernel_repair` takes arbitrary field
parameters, a query table `t`, explicit `Function.Injective t`, explicit
`noneOne : ∀ i, t i ≠ 1`, and the explicit condition that
`TwoSwapResidualSource.matrix ... t ht noneOne` has nonzero determinant. It
then produces coefficients for an exact combination of the selected
`AugmentedQuotient` columns that hits every requested selected 13-coordinate
source-shaped residual target. The combination has all 271 TwoSwap sparse
coins zero, evaluates to zero at each provided query root in all four slots,
has zero first fold at all 32 degrees, and has zero inactive balance.

R647 still has explicit point-1 and point-2 hypotheses for its separate
structured moment. The R651 result neither removes them nor establishes a
connection to every C1/H1/G target.

## Not proved

The following remain open: actual all-17/p0/p2 same-public target
compatibility; derivation of actual root conditions and a causal nonzero
probability law; actual source/native construction and callback execution;
and the full joint coverage, simulator, privacy, and soundness arguments.
No end-to-end privacy or security claim follows from this milestone.

## Evidence and release status

Evidence: [`evidence/r651-conditional-residual-kernel-repair/`](evidence/r651-conditional-residual-kernel-repair/).
The lead checked the exact sources, all saved attempt checksums and every accepted axiom report, then promoted the six successful sources byte-for-byte. The combined evidence is the release record; the earlier standalone R648 scratch package is not needed for replay. No unchanged compile was repeated.

## Release source pins and full axiom output

Exact target, source revision and source checksum are in `RELEASE_PINS.json`; full commands and resource measurements are in the receipts. Peak RSS is GNU time Lean-child RSS; wrapper cgroup peak is not aggregate Lean RSS.

```text
'AspisR19.R645TwoSwapHighDirections.actual_mask_coin' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisR19.R645TwoSwapHighDirections.actual_mask_transport' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisR19.R645TwoSwapHighDirections.actual_mask_balanced' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisR19.R645TwoSwapHighDirections.actual_selected_coins_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisV8R19.R647TwoSwapStructuredMoment.actual_sparse_pairing_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisV8R19.R647TwoSwapStructuredMoment.selected_structured_moment_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisR19.R648AugmentedTwoSwapKernel.actual_selected_coins_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisR19.R648AugmentedTwoSwapKernel.source_weights_mask_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisV8R19.R649TwoSwapResidualRepair.selected_residual_repair' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.AspisV8R19.R649TwoSwapResidualRepair.0.AspisV8R19.R649TwoSwapResidualRepair.observed_combination' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisV8R19.R650ResidualCombinationKernel.combination_sparse_coins_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisV8R19.R650ResidualCombinationKernel.combination_query_root_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisV8R19.R650ResidualCombinationKernel.combination_first_fold_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisV8R19.R651ResidualKernelRepair.residual_kernel_repair' depends on axioms: [propext, Classical.choice, Quot.sound]
```
