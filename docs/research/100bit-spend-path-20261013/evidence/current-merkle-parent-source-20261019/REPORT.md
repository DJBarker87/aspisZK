# Current Merkle source parent bridge — 2026-10-19

This packet extracts the current verifier's unchanged `merkle_path`, exact `Digest32` trait and exact `parent_with_digest` body from source parent `9abb1c0619c10997f75e461c015a2f6657817edd`. The complete original source files, selected spans and hashes, source-cut harness, LLBC, generated Lean, tool commands, admissions and receipts are retained.

The unchanged source extraction emits the whole checker but leaves the generic `core.array.from_fn` library boundary in its external template. An isolated source candidate replaces that child-building closure by eight explicit calls to the same pure child-selection body. This candidate extracts completely without an external-function template. It has **not** been adopted into production. Original/candidate source equivalence, its CU effect and release artifact remain open.

The exact parent helper body is unchanged by that candidate. Two focused checked proofs establish:

1. `RawMerkleParentCall.parent_equation`: the emitted parent helper equals the same dictionary digest call on exactly nine grouped parts, including errors/divergence. `parent_success` derives that digest success from actual parent success.
2. `RawMerkleParentBytes.parent_literal_bytes`: those arguments flatten to precisely `0x18 || child[0] || … || child[7]`, 257 bytes, matching the retained `AspisR1.Merkle32Path.nodeInput`. Its generic decomposition uses `List.ofFn_mul`; it does not normalize a concrete 256-byte recurrence.

Both proof targets report only `propext`, `Classical.choice`, and `Quot.sound`. No concrete SHA/random-oracle assumption is introduced. Digest functionality/global-log consistency remains a separate obligation.

| Focused target | Exit | Wall | Max process RSS | Cgroup peak | Swap |
| --- | --- | --- | --- | --- | --- |
| generated Types | 0 | 1.204 s | 2,622,568 KiB | 281,784,320 B | 0 |
| generated Funs | 0 | 1.705 s | 2,628,708 KiB | 286,416,896 B | 0 |
| RawMerkleParentCall | 0 | 1.604 s | 2,623,792 KiB | 284,037,120 B | 0 |
| RawMerkleParentBytes v3 | 0 | 1.705 s | 2,630,504 KiB | 291,160,064 B | 0 |

All four ran on the NUC under fresh aggregate admission, `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`, Lean 4.32.0, one thread and a 120-second watchdog. Exact revisions, source/object/import hashes and axiom reports are in the retained receipts. The byte proof's v2 diagnostic was a redundant tactic after its goal had already closed; v3 removes that tactic. Original source extraction and candidate extraction each have separate capped Charon/Aeneas evidence in their archives.

Still open: derive a full six-step ideal authenticated path from actual checker acceptance; bind all those calls to the single chronological global oracle log; finish the leaf decode/source correspondence; prove or adopt a source-equivalent replacement for the original `from_fn`; and run the required runtime/CU/artifact gates after any production adoption. These parent results do not complete the 100-bit soundness claim.
