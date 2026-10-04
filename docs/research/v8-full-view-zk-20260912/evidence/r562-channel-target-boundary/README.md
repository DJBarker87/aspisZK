# R562 channel target boundary — focused evidence

The green target is `R562ChannelTargetBoundary.GREEN.lean`, compiled as
`AspisV8R19/R562ChannelTargetBoundary.lean` in run `1791075818702541000`.

It contains two source-shaped field-model theorems.

- `structured_claim_zero` composes the existing complete
  `original_weights_transported_pairing` identity with explicit zero
  hypotheses for the retained mask, points 1 and 2, inactive balance, and the
  two image tails. The expression retains its literal tau updates.
- `structured_sparse_claim_zero` instantiates the mask with the exact
  `TwoSwapSourceG.original (maskWeights271 half z)` and the exact
  `TwoSwapSourceTable.order`; it uses R561's sparse pairing bridge rather
  than a dense power-row mixing construction.

Final result: exit 0; wall 0.96 s; peak Lean-child RSS 2,303,768 KiB; swap 0.
Scope: MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, TasksMax=128, Lean
-j1 -M4500. Complete final axiom reports list only `propext`,
`Classical.choice`, and `Quot.sound` for both theorems.

All four source snapshots, logs, receipts, import pins, and failure histories
are retained under `attempts/`. The final source revision is
`3458eb014bb1f78ad06b42c9662a13872c4b7006`; final source SHA-256 is
`700ab9ae95404bbc255bf1ef25ec6e7bc83abf0ee1232de2c6dc47d5817df468`.

Boundary: these are field-model algebraic consequences of their visible zero
hypotheses. They do not prove Rust writes or wrapping arithmetic, source
execution correspondence, that the hypotheses are attainable for every
prefix, joint image existence, privacy, soundness, or security. The first
remaining obligations are actual selected source bindings and universal joint
image existence.
