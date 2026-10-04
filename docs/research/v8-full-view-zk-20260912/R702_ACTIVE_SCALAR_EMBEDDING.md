# R700/R702/R703: active scalar embedding

Focused green targets:

- `AspisV8R19/R700ActiveBlockInverse.lean`: run `1791126171384442000`, exit 0, wall 0:01.42, RSS 3257384 KiB, swap 0, SHA256 `d319555a7f73cb9d4c656d3a95ed7f0a065c7ceac987b1ae871ecd2e371004bd`.
- `AspisV8R19/R702ActiveScalarEmbedding.lean`: run `1791126941121802000`, exit 0, wall 0:01.89, RSS 3284920 KiB, swap 0, SHA256 `8baf43401eb90595ed58c4375e7f95d5b8ef0b24b6daabed142e4a90b08c54f8`.
- `AspisV8R19/R703ActiveBlockMatrix.lean`: run `1791126783390322000`, exit 0, wall 0:01.37, RSS 3256536 KiB, swap 0, SHA256 `9861064212747471f6bb0fd3d69440ae2edc7f6693909b55edb1a225de3130ec`.

All used pinned Lean 4.32 with `-j1 -M4500`, `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, and `TasksMax=128`. Exact receipts, source snapshots, logs, the runner, route note, and direct source pins are in the evidence bundle.

R700 proves the generic distinguished-row block transform is an involution when every block has a unique distinguished row. R703 identifies that transform with a matrix, proves its square is identity, and proves its determinant nonzero under `Nontrivial F`. R702 instantiates the active high-coordinate layout: selected-channel coefficients reconstruct the per-block sums; `chosenQ` realizes the transform; column 697 and the corresponding quotient coordinate 1018 vanish; the top four quotient coordinates vanish; and the scalar source chord at `(a,b,c)=(2,0,0)` is twice the block transform on every high active row.

This is source-shaped finite-table and commutative-ring algebra. It does not prove the 214-row determinant, a normalized-circle nonvanishing condition, native scatter execution, actual H1 image coverage, legal C1/H1 compatibility, a simulator, oracle losses, privacy, or security. The next gate is the selected 214-minor and its normalized-circle restriction, followed by active-preserving H1 residual image and the actual source/causal proof obligations.

All failed changed R700/R702 drafts and their receipts/logs/source snapshots are retained. The completed axiom reports are standard `propext`, `Classical.choice`, and `Quot.sound` only. No successful target was rerun.
