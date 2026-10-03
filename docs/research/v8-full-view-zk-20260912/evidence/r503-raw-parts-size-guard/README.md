# R503 fixed-U64 positive-size quotient bound

The promoted Lean target is `lean/AspisV8R19/R503RawPartsSizeGuard.lean`.

The theorem `AspisV8R19.R503RawPartsSizeGuard.positive_size_quotient_bound` is an arithmetic lemma over fixed `U64` words. From `0 < size.val` and `n.val * size.val ≤ 9223372036854775807`, it proves that division of the fixed signed-64-bit maximum by `size` succeeds, identifies the quotient, and bounds `n.val` by it. It compiles with axioms `[propext, Classical.choice, Quot.sound]`.

This is not a proof about generic `Usize` or a native pointer. Although the captured Rust target records an eight-byte pointer, the source-to-ABI interpretation of the native type as this fixed-U64 model remains open. The lemma does not establish raw-parts source execution, alignment, pointer validity, slice construction, or error correspondence.

## Focused Lean run

- Source revision: `17b477689c72707405fa74bdb9ce22953dec41bb`
- Promoted source SHA-256: `529a7105d74eea604f4a370683068218ed9937d2985d9ea774eefee33ec6d52a`
- Target: `AspisV8R19/R503RawPartsSizeGuard.lean`
- Exit status: 0
- Wall time: 0.99 s
- Peak Lean RSS: 2,531,340 KiB
- Swap: 0
- Scope: `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`; Lean flags `-j1 -M4500`
- Exact output and runner receipt: `R503RawPartsSizeGuard.log` and `R503RawPartsSizeGuard.receipt.json`
- Imported local arithmetic source SHA-256 (`R489WordArithmetic.lean`): `ac6766da5acfc45ac29bfe3c00d927a495b2104c08b87f745356de1f77da04d5`

## Preserved rejected Usize attempts

Both earlier attempts are retained with their full logs and receipts. The literal attempt failed because the Aeneas `Usize` bound did not admit the signed-64-bit maximum. The platform-width attempt failed because Lean's `System.Platform.numBits` remained opaque, so `decide` could not establish 64-bit width. Neither attempt is part of the promoted theorem, and no platform-width axiom or premise is introduced.

## First remaining proposition

Prove the captured eight-byte target's native pointer/integer interpretation corresponds to the fixed-U64 representation, then prove the actual raw-parts source guard execution and its error-preserving behavior. This bridge is not assumed here.
