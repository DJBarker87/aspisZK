# R824 source block triangularity

Proves the exact predicate consumed by R825: `reorderedSourceMatrix.BlockTriangular blockLabel`. It transports the active-row lower-zero result across the row permutation, combines the 214 active rows with all eight supplementary rows using the finite raw-row dispatcher, and then rewrites each permuted row through `rowOrderInv (rowOrder i) = i`. The supplementary p0/p2 rows use R820; the other six have label 0, so their strictly-lower-column cases are impossible.

Exact target: `AspisV8R19/R824SourceBlockTriangular.lean`. Final source SHA256 `ca7175035a37cf5b8de411b9d7d4da9b93b08c031dc4c7691a1f3c0cc1d4c45a`. Green run `1791160406758179000-2d917e5ad955`: exit 0, wall 1.55 s, peak Lean RSS 3,360,292 KiB, swap 0, flags `-j1 -M4500`, cgroup MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, TasksMax=128. Full axioms: `active_lowerRow` and `source_block_triangular` each depend on `[propext, Classical.choice, Quot.sound]`.

Failed iterations retained: run `1791160362011768000-c10a81c6b624` omitted the direct R806 import; run `1791160390960060000-fddbc3dcfd85` imported R806 but omitted its namespace opening, leaving `blockLabel` unresolved. The final version adds the `open` and compiles.

Boundary: this proves triangularity of the fixed selected source matrix after the exact selected row/column permutations, using the compiled R823 active-row theorem and R820 supplementary p0/p2 source facts. It is not a determinant or privacy/security conclusion; those require subsequent diagonal-unit and block determinant assembly results and their source assumptions.
