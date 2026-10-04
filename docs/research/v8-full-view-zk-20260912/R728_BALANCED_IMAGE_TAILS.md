# R728: Balanced image tails

Canonical Lean target: `AspisV8R19/R728BalancedImageTails.lean`, SHA-256 `2642df89e896544e3635efb7f8a51fcc659d79503a3f4f682dcfcaa83a467f6d`. Final focused run `1791132336445131000` used source revision `5ac6e5ffcd955a6cad3bd7c05b7a5a67cadd6475`, Lean 4.32, `-j1 -M4500`, `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, and `TasksMax=128`.

The final target exited 0 in 0:01.48 with peak Lean-child RSS 3,335,448 KiB and swap 0. All four complete `#print axioms` reports contain only `[propext, Classical.choice, Quot.sound]`. The final compiler warning is retained verbatim in its raw log.

From explicit source-image conditions `q1023 = 0` and `b*q1022 - c*q1021 = 0`, inactive-balance zero, the final first-fold equation, and `b²+c² ≠ 0`, R728 proves all four top flattened coordinates 1020–1023 are zero. It also proves the exact circle factorization `b²+c² = (1+u²)(1+v²)` for `b=u*v-1`, `c=-(u+v)`, and its nonzero consequence under explicit denominator assumptions.

The evidence preserves the first focused proof failure `1791132298806857000` and the final green record `1791132336445131000`, with the direct R727 source pin and runner. This does not show that any source-image, balance, fold, or denominator condition is justified for the selected verifier. It makes no native-helper, privacy, or security claim.

The first remaining proposition is to justify the outside-CM31 denominator condition and the source-image, balance, and fold premises at the actual selected callback, and to finish the universal H1 point/relation correction.
