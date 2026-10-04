# R723: Active-kernel support

Canonical Lean target: `AspisV8R19/R723ActiveKernelSupport.lean`, SHA-256 `8bef6b836ff889ce160689d97f5d8d488369aed3bdb7352f55871865b27c2f70`. Final focused run `1791131297765619000` used source revision `dc4a83812c9b0c252412e5ba190cb4b6cb152a82`, Lean 4.32, `-j1 -M4500`, `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, and `TasksMax=128`.

The target exited 0 in 1.21 s with peak Lean-child RSS 3,324,120 KiB and swap 0. Its complete axiom report contains only `[propext, Classical.choice, Quot.sound]`.

For any commutative ring and quotient sequence `q` that vanishes from index 108 onward, R723 proves `sourceChord half q a b c (rowCode i) = 0` for every selected row. It applies the existing support theorem at `n=54` and the R721 exact finite layout bound `114 ≤ rowCode i`.

This is support-only algebra. It makes no relation, determinant, native, probability, privacy, or security claim. It is intended only for the remaining active-preserving H1 residual matrix work.
