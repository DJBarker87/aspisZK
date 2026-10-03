# R503 fixed-U64 positive-size quotient bound

R503 proves an arithmetic statement over fixed `U64`: for positive `size` and `n.val * size.val ≤ 9223372036854775807`, division of the signed-64-bit maximum by `size` succeeds and its quotient bounds `n.val`. It does not prove a generic `Usize` fact or actual raw-parts execution.

Final target: `AspisV8R19/R503RawPartsSizeGuard.lean`; source revision `17b477689c72707405fa74bdb9ce22953dec41bb`; source SHA-256 `529a7105d74eea604f4a370683068218ed9937d2985d9ea774eefee33ec6d52a`. Focused run `1791051448139367000` exited 0, wall 0.99 s, peak Lean-child RSS 2,531,340 KiB, swap 0. Complete axiom output is `[propext, Classical.choice, Quot.sound]`. The pinned Lean 4.32 job used `-j1 -M4500` and systemd limits MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, TasksMax=128.

The R506 dependent image proof also compiles and is recorded separately. No native pointer-to-U64 interpretation is asserted by either arithmetic theorem. The first remaining proposition is the captured 8-byte native ABI to fixed-U64 representation bridge, followed by actual raw-parts guard execution with every result/error branch preserved. The R501/R504 LLBC and current R495 inventories are source-capture context only; they do not close that bridge.

Exact source, failed Usize attempts, successful source snapshot, full logs/receipts, source captures, inventories, and recursive checksums are in `evidence/r503-raw-parts-size-guard/`. The captured verifier source and genuine 999,790 / 999,532 CU results are unchanged. End-to-end privacy and security are not claimed.
