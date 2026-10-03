# R464–R465: observed trace bound and accepted-value permutation

R464 bounds the length of the instrumented challenge trace. R465 proves a permutation law for accepted values in an abstract list model. The successful Lean inputs, logs, receipts, and shared runner are preserved in this evidence directory; the promoted source files match the saved successful inputs byte-for-byte.

R464 compiled `AspisV8R19/R464ObservedChallengeTraceBound.lean` at source revision `57b9ddbd829f532d2448709d96b4a38836e6ade1` (exit 0, wall 1.53 s, peak RSS 3,698,360 KiB, swap 0). Its two complete axiom reports are recorded verbatim in `evidence/.../R464/receipt.json`; both include `propext`, `Classical.choice`, `Quot.sound`, and `core.fmt.Formatter`.

R465 compiled `AspisV8R19/R465AllAcceptedPermutation.lean` at the same revision (exit 0, wall 1.40 s, peak RSS 3,231,760 KiB, swap 0). All three complete axiom reports are in its receipt and list `propext` and `Quot.sound`. Both jobs used `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`, and Lean flags `-j1 -M4500`; the receipts identify GNU time as the Lean-child RSS measurement.

The proved boundary is limited to the instrumented trace-length bound and the abstract all-accepted permutation law. The next proposition is the bridge to the actual four-coordinate sampler and shared-oracle freshness/collision behavior. This package makes no privacy claim.

The evidence manifest and `verify_evidence.py` check saved input identity, raw successful run records, complete axiom outputs, linked import hashes, and the package checksum index. No failed-run artifacts were present for these two run IDs.
