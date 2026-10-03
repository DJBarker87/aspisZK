# R506 fixed-U64 length-guard image

R506 proves the exact result image of its defined arithmetic program for arbitrary fixed `U64` inputs:

`lengthGuard n size = .ok (decide (n.val * size.val ≤ 9223372036854775807))`.

It preserves both true and false outcomes and proves the true-result corollary under the byte-size bound. The proof uses R503's positive-size quotient theorem; this is arithmetic over the supplied Aeneas fixed-U64 operations, not actual Rust pointer or raw-parts semantics.

Final target: `AspisV8R19/R506RawPartsLengthGuard.lean`; source revision `17b477689c72707405fa74bdb9ce22953dec41bb`; source SHA-256 `7b1999dd06ec82cb75217ae2a490efb99724cea0b37fc123286b798ecedde5be`. Focused run `1791052237791790000` exited 0, wall 1.06 s, peak Lean-child RSS 2,543,300 KiB, swap 0. Both complete axiom reports contain `[propext, Classical.choice, Quot.sound]`. The pinned Lean 4.32 job used `-j1 -M4500` and systemd limits MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, TasksMax=128.

The first remaining proposition is the native ABI-to-fixed-U64 representation bridge, then a source-preserving proof that the actual raw-parts guard corresponds to this image, including its failure cases. The current source inventories and LLBC captures identify relevant source declarations but establish no such correspondence. Full privacy and security are not claimed.

Exact source, every successful and failed focused attempt, logs, receipts, and complete axiom output are under `evidence/r506-raw-parts-length-guard/`.
