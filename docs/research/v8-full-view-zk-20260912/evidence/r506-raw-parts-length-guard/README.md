# R506 fixed-U64 length-guard arithmetic

Promoted scratch candidate: `docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/R506RawPartsLengthGuard.lean`.

The final focused target proves an exact image theorem for the defined Aeneas `U64` arithmetic program:

`lengthGuard n size = .ok (decide (n.val * size.val ≤ 9223372036854775807))`.

It also proves the corollary that the result is `.ok true` when the byte-size inequality holds. The image theorem preserves the false result outside that bound. The proof splits on zero versus positive `size.val`; in the positive branch it uses R503's fixed-U64 quotient result. This package makes no native pointer or source-execution claim.

## Final focused run

- Source revision: `17b477689c72707405fa74bdb9ce22953dec41bb`
- Target: `AspisV8R19/R506RawPartsLengthGuard.lean`
- Final source SHA-256: `7b1999dd06ec82cb75217ae2a490efb99724cea0b37fc123286b798ecedde5be`
- Exit status: 0
- Wall time: 1.06 s
- Peak Lean RSS: 2,543,300 KiB
- Swap: 0
- Scope: `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`; Lean flags `-j1 -M4500`
- Complete axiom output for both the image theorem and positive-bound corollary: `[propext, Classical.choice, Quot.sound]`
- Exact source snapshot, log, and receipt: `attempts/1791052237791790000.*`
- Direct local import R503 source SHA-256: `529a7105d74eea604f4a370683068218ed9937d2985d9ea774eefee33ec6d52a`

All R506 focused attempts are retained under `attempts/` as exact source snapshots, logs, and receipts, including eight earlier worker failures, two lead failures, an earlier successful positive-bound-only proof, and the final successful image proof. The final run is the only run that proves the exact image theorem without `sorryAx`.

## First remaining proposition

Show that the captured eight-byte target's native pointer/integer representation corresponds to fixed `U64`, then connect the actual raw-parts length guard execution to this arithmetic definition while preserving every result branch. Neither bridge is claimed here.
