# Wide source CM map v1

This source-only packet records same-call, full-Result maps from the transparent Wide extraction cut’s `CM31.add`, `CM31.sub`, and `CM31.mul` into the actual QMMul extraction cut. It also bridges the nested `M31.reduce_u64` wrapper. The maps preserve success/failure/divergence. This is a cut-to-cut source correspondence, not a checked CurrentWide refinement claim.

Lean target exited 0 in 8.797 seconds; peak process RSS was about 2.242 GB and swap was zero. `#print axioms` for all four exported theorems reports only `[propext, Classical.choice, Quot.sound]`. Compiled objects are omitted.
