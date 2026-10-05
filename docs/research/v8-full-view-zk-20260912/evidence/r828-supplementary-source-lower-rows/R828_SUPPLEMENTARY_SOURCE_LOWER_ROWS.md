# R828 supplementary source lower rows

`lowerRow r` states that every matrix entry in the reordered row `rowOrderInv r` is zero in columns whose block label is smaller than that row label. `supplementary_lowerRow` proves this for all eight non-active source rows. The p0 and p2 rows map to flat rows 73 and 72, both label 6, and use the existing R820 lower-zero theorems. The other six rows map to flat rows 0 through 5, all label 0, so there is no column with a strictly smaller label.

This is an index-and-entry boundary for the eight supplementary rows; it does not prove full block triangularity.

Final focused target `AspisV8R19/R828SupplementarySourceLowerRows.lean` compiled with exit 0, wall 1.64 s, peak Lean RSS 3,349,996 KiB, swap 0, pinned Lean flags `-j1 -M4500` under MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, TasksMax=128. Full printed axiom reports: `lowerRow` depends on `[propext, Classical.choice, Quot.sound]`; `supplementary_lowerRow` depends on `[propext, Classical.choice, Quot.sound]`.

All three attempts are retained: two failed proof iterations, then the green focused target. The first failed at label simplification and whnf timeout; the second failed to rewrite a row value through the unreduced matrix submatrix application and printed `sorryAx` for that failed target. The final proof rewrites the matrix application explicitly, then uses the literal flat-row-to-source-row equalities.
