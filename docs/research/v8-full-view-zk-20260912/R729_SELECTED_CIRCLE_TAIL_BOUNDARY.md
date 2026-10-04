# R729: Selected circle tail boundary

Canonical Lean target: `AspisV8R19/R729SelectedCircleTailBoundary.lean`, SHA-256 `5c5063a22a0e9c2063a4e262f4dd38ce4caec388786e4384981ba5bbd6d0c9f9`. Final focused run `1791132501021457000` used source revision `5ac6e5ffcd955a6cad3bd7c05b7a5a67cadd6475`, Lean 4.32, `-j1 -M4500`, `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, and `TasksMax=128`.

The final target exited 0 in 0:02.55 with peak Lean-child RSS 3,328,584 KiB and swap 0. Both complete `#print axioms` reports contain only `[propext, Classical.choice, Quot.sound]`.

For exact QM31 values `u` and `v` with nonzero imaginary coordinates, R729 proves `(u*v-1)^2 + (-(u+v))^2 ≠ 0` by `SamplerCirclePolicy.outside_has_denominator` and R728's circle-norm factor. It then specializes R728's tail result at `a=1+u*v`, `b=u*v-1`, and `c=-(u+v)`. The source-image equation, inactive-balance equation, last first-fold equation, and top-coordinate premise remain explicit.

The failed initial focused record `1791132476187556000` and final green record `1791132501021457000` are retained with direct R728 and sampler-policy sources. This does not prove that a selected native sampler success establishes the two imaginary-coordinate premises at this callback. It makes no whole-callback, oracle, privacy, or security claim.

The first remaining proposition is to bind successful actual circle conversions and their original parameters into the selected callback, retain the source-image/balance/fold premises, and finish the universal H1 point/relation image.
