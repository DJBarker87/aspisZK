# SpendDataMap focused Lean evidence

This bundle preserves the four focused attempts for `R1SpendDataMap`. Attempts a–c failed during proof development; attempt d compiled successfully from the exact source snapshot included here. The module defines coordinate maps for digest, path, pair leaf, witness, and public statement, and proves witness identity/composition plus public-map identity/composition. It does not assert that an arbitrary scalar function preserves spend equations.

Attempt d exited 0 in 1.79 s with peak RSS 3,326,364 KiB and zero swap. The runner recorded `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`, and `TasksMax=128`. The four `#print axioms` reports are preserved; witness laws depend on `propext`, while public-map laws report no axioms.

The direct import `R1SpendRelation` source and object are included with hashes in the manifest. The green target object and direct import object are also in the deterministic object archive. The runner receipt does not record a git revision, so the manifest records the packaging base separately and does not claim it as the compile-time revision.
