# D79 additional tx1 binding classes (2026-10-20)

Branch `codex/cx-record-classes-20261020`, parent
`f47037375f1b02492aee023616ed4c553a16d8d4`. Existing Lean modules and Rust
sources are unchanged. Paths below are repository-relative; `lean/` and
`evidence/` abbreviate this research directory.

| Digest input | Fixed bytes | Source and checked definition |
|---|---:|---|
| Stored compact proof | 57,607 | `crates/aspis-r1-cost-probe/src/compact.rs:26`–`:69` defines offsets, compact widths and padded slots; `candidate.rs:40` guards `PROOF_BYTES`. `lean/WireBindingRecordCodec.lean:12` mirrors this arithmetic; `:20` proves its value. This is the adopted compact length, not retired `eight_way_proof_bytes`. |
| Original ASF8 account | 1,880 | `crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs:33`, `:403`, `:822`; late size = 32+800+688 (`pair_tree_profile.rs:385`, `:392`, `:393`; `pair_terminal.rs:37`), payment = 216 (`payment_relation.rs:28`). `lean/BinWireBindingLengths.lean:27` obtains the length and both exclusions from retained decoder success, via `BinWireEnvelopeLengths.lean:12`. |
| Checksum domain + body | 1,758 | `crates/aspis-r1-cost-probe/src/verifier.rs:273`–`:284`: domain 22 + body 1,736. `lean/WireBindingRecordCodec.lean:25`, `:40`, `:67`, `:75` constructs these bytes and proves their length. S2 weights have 64 entries (`transport.rs:8`, `:9`; `verifier.rs:93`), each 16 bytes. The final 32-byte checksum is excluded from its own input; complete checkpoint size is 1,768 (`verifier.rs:18`, `:32`). |

`BindingRecord` carries the actual bytes of these three classes; its checksum
constructor takes the typed body rather than an assumed length. Every class
excludes 65 and 31 (`WireBindingRecordCodec.lean:104`, `:108`). Soundness
proves binary-node and 31-byte-frame separation at
`BinWireBindingLengths.lean:36`, `:42`. The new privacy module
`docs/research/v8-r0-zk-20261009/lean/R1Z/WireBindingLengthsR1PBin.lean:14`
proves the three fixed lengths, and `:42` extends D79's concrete transcript
separation with all three binding inputs.

`Tx1Class` (`WireBindingRecordCodec.lean:114`) includes every transcript,
salted-leaf, binary-node and checkpoint class in WIRE-TX1.
`evidence/record-classes-20261019/source-classes.json` maps all **31**
syntactic digest sites to this list, with 28 source pins. Classification
implies separation from binary nodes for every non-node class, on both trees.

Final local packet: `evidence/record-classes-20261019/manifest.json`, 15
theorem audits, 12.01 s total, peak 3,261,874,176 bytes, zero swaps. Final J
attempts **6302–6303**: 1.07/1.59 s, peaks 1,343,184/3,368,096 KiB, zero
swaps; 14 audits. All final axioms are subsets of `{propext, Classical.choice,
Quot.sound}`. Receipts, historical attempts and resolved dependencies are
alongside the manifest. New shared codec source/object was snapshotted before
replacement on J; its sole dependent was rebuilt. No existing `*Bin` root
imports it, so no existing root changed or required replay.

The source-class mapping and codec widths do not prove deployed execution
membership. Whole-tx1/checkpoint extraction, compact parser refinement and
R-wire composition remain open. ASF8 admission still comes from the Pool
caller (`programs/r1-cost-probe/src/r1_pool_adapter.rs:962`, `:981`);
`candidate::tx1` alone permits arbitrary `public_bytes`. No unconditional
API-wide length claim is made. No false new target was found.
