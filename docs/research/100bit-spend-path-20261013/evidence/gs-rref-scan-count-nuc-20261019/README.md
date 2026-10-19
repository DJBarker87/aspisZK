# Counted production RREF pivot searches, verified on NUC

The counted companion mirrors the actual rrefLoopData fuel branches and uses the accepted counted pivot search. It threads exactly the same data and pivots through the production swap/normalize/eliminate calls and recursively adds the current scan count. The first projection equals the production loop result. Total candidate-row visits are at most fuel*rows; the standard initial fuel cols+1 gives (cols+1)*rows.

This counts the whole loop's pivot-search iterations. It does not yet count row-update cells, field operations, array copying, witness construction or bit complexity. Those remain separate components of the full extractor efficiency proof.

The changed source passed on the dedicated Linux NUC using the same native Lean 4.32 and CompPoly caches, without dependency builds. Exit 0; Lean time 0.86 seconds, controller wall 0.932 seconds; process peak RSS 1,654,370,304 bytes; swap 0. All three theorem axiom reports are standard-only. MemoryHigh 6G, MemoryMax 8G, MemorySwapMax 0; exact admission snapshot, command, preflight, source/object hashes, compiler and revision are retained. Sampled cgroup peaks are not substitutes for the larger process peak RSS. Native compiled objects remain in the task cache rather than Git.

The resource watcher was corrected before the accepted attempt to exclude its own scope from existing reservations and add its cap exactly once. Earlier controller refusals happened before Lean; proof attempts exposed small local equality rewrites and are not counted as accepted gates. No cap increase or unchanged regression was used. Full dense/extractor cost and the complete 100-bit soundness, privacy and two-transaction release obligations remain open.
