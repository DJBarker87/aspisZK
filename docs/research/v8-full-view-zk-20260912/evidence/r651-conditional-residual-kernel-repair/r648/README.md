# R648 Augmented TwoSwap kernel — scratch evidence

Final target: `AspisV8R19/R648AugmentedTwoSwapKernel.lean`. Final focused run
`1791111277391648000`: exit 0; wall 1.01s; peak Lean-child RSS 2,331,268 KiB;
swap 0. Both printed theorems use only `[propext, Classical.choice, Quot.sound]`.

The exact result takes arbitrary `t : Fin 22 → F`, explicit
`Function.Injective t`, and explicit `noneOne`. For all 13 selected
`TwoSwapWitness.degree/slot` columns, it proves that the actual TwoSwap sparse
coin read of `actualMask` is zero. The proof derives degree ≤30, shows the
flattened quotient is zero from raw index 124, uses `sourceChord_support` with
n=62, then uses R645's TwoSwap `actual_mask_coin`. It also proves the actual
`TwoSwapSourceWeights.mask` definition equals R645 `actualMask` by rfl.

Boundary: exact field/table model only. This does not prove actual q22
injectivity or `noneOne`, source/native construction, residual determinant
coverage, universal same-public target coverage, callback/oracle behavior,
privacy, or soundness.

Attempts `1791111235409163000` and `1791111257448902000` retain ordinary
mechanical proof errors; the final source/log/receipt is preserved without a
rerun. Scratch-only; not promoted, staged, committed, or pushed.
