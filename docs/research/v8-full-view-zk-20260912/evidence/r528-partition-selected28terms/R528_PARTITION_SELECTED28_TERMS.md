# R528 selected 28-term partition

Focused target `AspisR528PartitionSelected28Terms/R528PartitionSelected28Terms.lean`,
source SHA-256 `e740eb531dd2954bae7a023efe07665ee92b260a2e2f1f1fe02d815dc38a93ad`,
compiled on source revision `20175e063c189d1239b95ebfe99b05c2c67d24b8` with exit 0, wall 0:01.55,
peak RSS 3,704,320 KiB, and zero swap. The final source, receipt, raw log,
and complete `#print axioms` outputs are retained under `focus-records/`.

`selected28_groups_flatten` proves that the seven groups of four exact indexed
terms, formed as nested `List.ofFn` calls and flattened, equal `List.ofFn terms`
in source order. The proof is generic in the term type and uses finite-list
construction plus index arithmetic; it does not evaluate term values.
`selected28_source_slots` reuses `SharedGammaDots.source_indices` to establish
the one-based slot bound `1 + 4*k + j < 29` for the selected group coordinates.

The complete axiom report is `[propext, Quot.sound]` for the flatten theorem
and `[propext, Classical.choice, Quot.sound]` for the slot theorem.

This is list routing and index arithmetic only. It does not establish a native
array loop, storage behavior, optimized selected source execution, or any
callback/preparation correspondence. The first remaining source obligation is
execution of the actual selected group construction and update loop.
