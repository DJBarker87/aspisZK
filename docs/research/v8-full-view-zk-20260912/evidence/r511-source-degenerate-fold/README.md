# R511 degenerate source-shaped fold compatibility

The final Lean target proves an algebraic fold and kernel-zero subclaim for every `t : Fin 22 → F`, including repeated values, and every `alpha : F`, including zero. It uses the exact source-shaped `finished` and `sourceQuotient` definitions. The theorems establish slot-factor identity, first-fold zero for selected columns (using the actual nonzero `SparseHighWitness.slot`), and kernel zero for both individual columns and their selected linear combinations extended to 256 blocks.

This is not a raw-query zero theorem, legal-mask coverage, proof of the full joint C1/H1/G compatibility condition, Rust execution correspondence, or a privacy proof. R513 now proves the root-zero subclaims without distinctness. The next missing proposition is legal G-read preservation, followed by universal target coverage for joint C1/H1/G compatibility.

Final target: `AspisV8R19/R511SourceDegenerateFold.lean`; source revision `f6b4dd9e03d257a0e1a71f90f2f30b887933813d`; source SHA-256 `71512d9f120422d367282ba5ed35d38107a38453d987fe574c88ef29ed698ee2`. Final run `1791053023435294000` exited 0, wall time 1.16 s, peak Lean-child RSS 2,303,048 KiB, swap 0. It used the pinned Lean 4.32 cache, `-j1 -M4500`, MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, TasksMax=128. All eight complete `#print axioms` outputs contain only `[propext, Classical.choice, Quot.sound]`.

Every focused attempt is retained under `attempts/` as source snapshot, full log, and receipt: initial worker failure, earlier worker green, lead green, weaker-premise failure, and final green.
