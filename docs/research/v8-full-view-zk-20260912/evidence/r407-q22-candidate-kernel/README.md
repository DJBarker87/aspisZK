# R407 q22 candidate kernel evidence

The promoted theorem relates the projected result of the exact bounded q22 scan under the independent-answer interpreter to a recursively defined result kernel driven by eight jointly uniform 18-bit candidates per block. The equality holds for every starting `ScanState`. The recurrence uses the literal scan updates, including duplicate handling, the boolean stop flag, and the 64-draw cap, and preserves the result including its failure count. It compares the projected result, not the returned transcript state or a full-trace distribution.

It does not prove the shared memoized-oracle law, uniformity of accepted tuples, or a security bound. The next stated bridge is cache-hit loss and kernel relabelling/uniform-success-query law.

The raw compile receipt is preserved unchanged. It lists only `R402Q22IndependentLaw` as a direct local import because the R406 source had not yet been promoted locally at receipt time. `dependency-cache-identities.json` records a separate read-only lookup of the R406 source and cached object identities; it does not rewrite the receipt or claim an in-run cache snapshot.

The compile used the pinned R126 Lean 4.32 cache, with `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`, and `-j1 -M4500`. It exited 0 in 1.40 seconds with 3,234,472 KiB GNU-time Lean-child peak RSS and zero swap. Both complete axiom reports use only `propext`, `Classical.choice`, and `Quot.sound`. `verify_evidence.py` checks the saved source, receipt, log, dependencies, report, and package checksums without running Lean.
