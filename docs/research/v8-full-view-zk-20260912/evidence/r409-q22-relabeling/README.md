# R409 q22 relabeling evidence

The final theorem proves relabelling invariance of the entire bounded independent-answer candidate kernel from the empty scan state, for any block fuel `n`, under an arbitrary permutation of `Fin (2^18)` extended to `Nat`. The scan/keep/finish operations commute with that relabelling; stopping behavior, the 64-draw cap, and failure counts remain unchanged.

This is a kernel symmetry result. It does not prove uniformity of successful tuples, a law for the shared memoized oracle, or a numerical probability claim. The next stated bridge is successful-query mass normalization together with shared-oracle cache-hit loss.

Both compile attempts are retained exactly. The first failed attempt includes `sorryAx` in downstream reports; the final source is byte-identical to the green capture. The successful run exited 0 in 1.48 seconds with 3,235,524 KiB GNU-time Lean-child peak RSS and zero swap under `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`, `-j1 -M4500`. All seven complete axiom reports use only `propext`, `Classical.choice`, and `Quot.sound` (the first three need only `propext` and `Quot.sound`).

The original successful receipt is preserved unchanged. It has an empty direct-local-import map because R407 had not been promoted locally at receipt time. The supplemental read-only dependency record identifies the R407 source and cached object and Mathlib's `Equiv.Basic` source/cache objects without claiming an in-run cache snapshot. `verify_evidence.py` only checks saved bytes and metadata.
