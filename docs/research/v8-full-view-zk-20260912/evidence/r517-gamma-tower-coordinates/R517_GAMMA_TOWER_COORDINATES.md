# R517 gamma tower coordinates

The final focused target is
`AspisR517GammaTowerCoordinates/GammaTowerCoordinates.lean`, source SHA-256
`82c667f44f4383ceb2b5e4954a4c8313527d4d670ae6997554d24a9fd6329263`
(checksum reproduced in `SHA256SUMS.txt`). It compiled on the pinned cached
host with exit 0, wall 0:01.71, peak RSS 3,250,432 KiB, and zero swap.
`focus-records/aspis-focus-1791053825007680000.*` preserves the exact source,
receipt, log, and complete four `#print axioms` outputs.

It defines coordinate conversion between
`AspisV8R17.QuadraticTowerOperations.Q R` and `Fin 4 -> R`, proves the two
conversions inverse, coordinate addition, and:

```
coords (x * y) = AspisV8.SemanticCarry.towerMul (coords x) (coords y)
```

The multiplication proof rewrites only through the existing `qmul_eq`, then
unfolds the existing explicit tower operations and uses ring normalization.
Its complete axiom reports use only `propext`, `Classical.choice`, and
`Quot.sound`; there are no additional axioms.

This is an algebraic bridge between the reused channel formula and existing
selected tower arithmetic. It does not prove native optimized-kernel execution,
array loops, raw arithmetic, callbacks, or source correspondence.

The initially missing cached `QuadraticTowerOperations` object is retained as
failure `1791053770900814000`; the exact unchanged source leaf was then
compiled as focused prerequisite `1791053786305358000` (exit 0, 0:01.00,
1,192,084 KiB RSS, zero swap). The subsequent changed-target syntax/name
failures are also retained before final success. No broad replay was run.
