# Unrolled wide limb normalization evidence

This bundle records a focused normalization theorem for `from_limbs_unrolled` on an eight-entry `Array.make`. The final module is `R1UnrolledWideLimbChecks`; its direct import is the retained generated module `UnrolledWideParserSource` (without an `R1` prefix), whose source and cached object are hash-pinned here and linked to its predecessor evidence.

Seven compile attempts have complete source snapshots, receipts, logs, time logs, and sidecars: the initial attempt `limb-check-a` under module label `UnrolledWideLimbChecks`, six corrected-module attempts `c` through `h`, of which only `h` passed. The `b` suffix has an empty wrapper preflight snapshot and no compile receipt or log: a first wrapper call used the corrected target name before its source file had been staged, leaving the snapshot path; the wrapper then refused to overwrite it. This is explicitly not counted as a compile attempt.

The final result was exit 0, wall time 2.20s, peak RSS 2,610,520 KiB, zero swap, with `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`, and `TasksMax=128`. Its sole `#print axioms` report lists `propext`, `Classical.choice`, and `Quot.sound`. No byte-level parser refinement or runtime claim is included.
