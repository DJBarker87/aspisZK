# First-fold restoration focused compile

`FirstFoldRestoration.lean` compiled as `R1FirstFoldRestoration` in the pinned
`aspis-r1-concrete-decoder-20261013` cache. Successful attempt e used source
SHA256 `d2af8991a2eab7531f699b16361a6810e3342b3c061d4f968932bb5041c3e576`,
exited 0 in 1.41 s, peaked at 2,891,880 KiB RSS, and used zero swap. The scope
was capped at `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`, `TasksMax=128`
with Lean threshold 5000 MB. `#print axioms` for `coefficientLane_join`,
`fold_join`, and `restore` reported `[propext, Classical.choice, Quot.sound]`
with no `sorryAx`.

The proof defines the interleaved `join`, establishes its four coefficient
lanes and final-message fold, then uses `parentIndex_mem_of_mem_fullQuartetSet`,
the first-fold encoded-channel identity, and injectivity from the stored fibre
inverse to recover each original child symbol. This is an algebraic implication
from the stated agreement-set inclusion; it adds no cryptographic premise or
soundness claim.

Imports include `Wide.EncoderLinearity` for its existing
`AspisWide.Agreement.exactFinalMessageCurve` declaration and
`Mathlib.AlgebraicTopology.SimplexCategory.Basic` to close the generated
Fintype dependency in the cached declaration. The latter has the same missing
generated-instance issue documented for `R1FinalResponses`.

Failed attempts a-d and their hashes, logs, timings, and receipts are retained
alongside e. `R1ParentSupport` attempt a was also compiled (exit 0, 1.09 s,
2,193,248 KiB RSS, zero swap); the existing green `R1FirstFold` attempt a and
`R1FoldCoefficientBridge` attempt b receipts are included for dependency
traceability. These are focused target results, not a package-wide replay.
