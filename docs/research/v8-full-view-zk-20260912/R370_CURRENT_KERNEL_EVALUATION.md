# R370: coefficient-kernel evaluation

R370 proves a generic exact-field identity for the coefficient kernel. The pairing uses the declared quarter factor and reversed slot `(4 - t) % 4`, which orders the four slots as `[0, 3, 2, 1]`. It rewrites `kernelEval` as the quarter times the sum over rows of `firstFold * dualFold`; if every `firstFold` is zero, `kernelEval` is zero.

The proof is over an arbitrary commutative ring and the kernel/model declarations in `FullCoefficientBoundary` and `BetaUniformCorrection`. Saved source excerpts document the coefficient expansion and reversed-slot convention. They do not establish Rust execution correspondence or a correction-existence result.

The successful focused check was run `1790948960291744000`: exit 0, 1.19 s, peak RSS 2,300,616 KiB, swap 0. It used systemd `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`, and Lean flags `-j1 -M4500`. The three complete `#print axioms` reports contain only `propext`, `Classical.choice`, and `Quot.sound`. Two failed drafts are preserved with their sources, logs, receipts, and `sorryAx` reports.

This result makes no Rust execution, correction-existence, universal joint-law, or security claim. See the [evidence bundle](evidence/r370-kernel-evaluation/README.md) for run records, source inventories, and the portable verifier.
