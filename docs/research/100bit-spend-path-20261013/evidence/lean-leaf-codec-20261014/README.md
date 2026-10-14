# Leaf codec focused Lean evidence

This bundle preserves the seven focused R1 leaf-codec modules and every receipt-backed attempt from the pinned NUC workspace. It is source/build provenance for fixed-width field and leaf encoding lemmas only; it makes no Rust refinement, protocol-acceptance, privacy, or release-closure claim.

Base source revision: `d08448d3a0bcd78a777217eaa6594fc658115cc2`. The source manifest records exact attempt snapshots and receipts, final source and object hashes, runner hashes (including `run2.py`), and the unreceipted zero-byte checkpoint-a source artifact separately. There are 18 receipt-backed attempts: 11 failed and 7 final, with no other successful attempt classified as superseded. Two failed import-only probes are retained as failed attempts and are not final target modules. The spelling of the `R1ExactLeafFieldCodec` final receipt is the observed `exact-leaf-field-c` (the earlier proposed `exact-leaf-field-codec-c` tag did not exist); the matching green receipt identifies the correct target and source hash.

All seven final attempts used `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`. Resource receipts are:

| Module | Attempt | Exit | Wall | Peak RSS | Swap | Axiom reports |
|---|---|---:|---:|---:|---:|---:|
| `R1FixedWidthEncoding` | `fixed-width-encoding-c` | 0 | 0:00.65 | 1,503,900 KiB | 0 | 2 |
| `R1RetainedFieldByteCodec` | `retained-field-byte-codec-a` | 0 | 0:01.80 | 3,329,936 KiB | 0 | 6 |
| `R1ListFieldCodec` | `list-field-codec-e` | 0 | 0:01.53 | 3,318,076 KiB | 0 | 6 |
| `R1RetainedExactLimbCodec` | `exact-limb-retained-b` | 0 | 0:01.50 | 3,324,960 KiB | 0 | 0 |
| `R1ExactLeafFieldCodec` | `exact-leaf-field-c` | 0 | 0:01.51 | 3,320,060 KiB | 0 | 8 |
| `R1MixedLeafEncoding` | `mixed-leaf-encoding-a` | 0 | 0:01.65 | 3,323,540 KiB | 0 | 8 |
| `R1LeafCodecCheckpoint` | `leaf-codec-checkpoint-b` | 0 | 0:01.31 | 3,301,336 KiB | 0 | 34 |

The final sources contain 64 `#print axioms` reports in total. The exact-limb module emitted zero reports by itself; the dependent checkpoint carries 34 reports for the checkpoint declarations, including the relevant final dependency audit. The zero-byte `R1LeafCodecCheckpoint-leaf-codec-checkpoint-a.source.lean` has no receipt, is marked `compiled: false`, has its empty-file SHA-256 in the manifest, and is not counted as an attempt. `source-manifest.json` lists all seven final modules and complete receipt-backed attempt classifications. The deterministic object archive contains only those seven final `.olean` objects.
