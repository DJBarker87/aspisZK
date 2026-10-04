# R561 sparse-G pairing — focused proof evidence

## Result

`R561SparseGPairing.GREEN.lean` compiled successfully as
`AspisV8R19/R561SparseGPairing.lean` in focused run `1791075464264831000`.

It proves, for every field `F`, arbitrary `weights : Fin 271 -> F`, and
arbitrary `m : Fin 1024 -> F`, that the exact `TwoSwapSourceG.original`
scatter pairs with `m` as

```
sum_r original weights r * m r
 = sum_i weights i * m (order (coinIndex i)).
```

It also specializes `weights` to `maskWeights271 half z` and connects that
identity to the existing `maskWeights271_dot` source-mask-loop theorem using
`sparseSlices m j = m (order (coinIndex <j,...>))` for `j < 271`.

The proof uses `TwoSwapSourceG.original_at`, `coinIndex_injective`,
`SparseGScatter.updates_off`, `MaskSourceSlices.maskCoins271_reads`, and
`MaskWeightVector.maskWeights271_dot`. It does **not** use dense
`SourceMixHorner` / `mixedSourceCoins`.

## Exact green result

- Target: `AspisV8R19/R561SparseGPairing.lean`
- Source revision: `2a53ea51fa562639281de5c2e7ffa982d6146699`
- Source SHA-256: `2fa3fc771ac16e2512ac0bea523beae3b2d5b1afb0d892bf66a41c02f80d386c`
- Exit: 0; wall: 1.04 s; peak Lean-child RSS: 2,306,540 KiB; swap: 0
- Scope: `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`,
  Lean `-j1 -M4500`.
- Complete axiom output: both final theorems depend only on
  `[propext, Classical.choice, Quot.sound]`; the exact output is in the green
  receipt and raw log.

## Attempts and dependency

- `attempts/1791075358025004000`: exit 1 before elaboration because the
  cached `MaskSourceSlices.olean` was absent.
- `dependency-mask-source-slices/1791075365980042000`: focused direct
  dependency build, exit 0, 0.91 s, 2,048,712 KiB RSS, swap 0; its full axiom
  report is retained.
- `attempts/1791075430923140000`: exit 1; first proof-shape correction.
- `attempts/1791075454546584000`: exit 1; finite-sum direction correction.
- `attempts/1791075464264831000`: final green result above.

## Boundary and next obligation

This is an exact field-model scatter/pairing identity. It does not prove the
actual Rust writes or arithmetic, a source-execution correspondence, rank or
image coverage, query behavior, privacy, soundness, or security. The first
remaining boundary is the actual selected sparse scatter execution and its
connection to this field-model representation.
