# Fixed-width list reconstruction focused compile

This bundle records the focused compile of `R1FixedWidthReconstruction.slices_flatten` on the pinned NUC Lean workspace. The theorem reconstructs a list by flattening all consecutive `k`-element windows, under the sole length premise `bytes.length = n * k`; its proof explicitly covers zero dimensions and uses `List.ofFn_mul` for the positive case.

The source base was `8b62ca762b89b5af8f131d1c97a5c6d400df2a6b`. The final source is SHA-256 `1b71a52cad69e57c163d77e4e0707ba84697c6082da30c75ff12ba9e86c1759`. Attempt `fixed-width-reconstruction-g` exited 0 in 0.88 seconds, with peak RSS 1,511,944 KiB, zero swap, and `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`. The final `#print axioms` output was `[propext, Quot.sound]`.

Attempts a–f are preserved as failed snapshots with their receipts and logs. The manifest records every attempt and the source/runner/object hashes. This is a focused theorem compile result only.

Pinned runner environment SHA-256: `d2f7294550dbdd9aa1cab186f25809c1a8b5a84d2fef74e3b3234052ced16c12`.
