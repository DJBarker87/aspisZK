# J1 opening-good checkpoint (2026-10-15)

This checkpoint records twelve focused Lean targets with 44 public `#print axioms` reports. Every successful report in this set contains only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`. The evidence is split across the linked bundles; target-level rows below list the successful source hash, compile receipt, and report count. Failed attempts remain in those bundles and are not counted as successes.

| Target | Successful source SHA-256 | Successful attempt / wall / peak RSS | Reports | Evidence |
|---|---|---:|---:|---|
| `R1LiteralStageFacts` | `d22fa3b460a991f1e6f1d092060713dd31671ecbc264583c38841e49ca9dfd08` | `b` / 1.60 s / 3,581,616 KiB | 5 | [stage facts bundle](../evidence/lean-literal-stage-facts-20261015/source-manifest.json) |
| `R1LiteralStageMessageCongr` | `26a1c96dd4c710473bff89549d3cd07f61b3ef6c841538adb477dc26ff884165` | `a` / 1.84 s / 3,587,280 KiB | 6 | [stage facts bundle](../evidence/lean-literal-stage-facts-20261015/source-manifest.json) |
| `R1LiteralMatchingFacts` | `e0528b64d56923e7d4c47b14c6a9e2f1f7a0a72ab15cb4b1ccf3fa7bf8bd86b5` | `b` / 2.21 s / 3,593,748 KiB | 1 | [matching facts bundle](../evidence/lean-literal-matching-facts-20261015/source-manifest.json) |
| `R1LiteralGammaSample` | `2845283741751a7088bd44a1f95700e164007761588f53889219587149b5a566` | `b` / 1.57 s / 3,598,288 KiB | 1 | [gamma sample bundle](../evidence/lean-literal-gamma-sample-20261015/source-manifest.json) |
| `R1LiteralOpeningCoherence` | `166f9485d04f3803d1330ae31e35279b7773af3cd5cf814552c3d21e1ba8aa03` | `a` / 1.67 s / 3,592,468 KiB | 11 | [opening binding bundle](../evidence/lean-literal-opening-binding-20261015/source-manifest.json) |
| `R1LiteralOpeningBinding` | `314840d5d543ec1c9207c057f6afeb7b5c160b3e41f8b695bfe4c5aa3d33b537` | `a` / 2.53 s / 3,592,220 KiB | 4 | [opening binding bundle](../evidence/lean-literal-opening-binding-20261015/source-manifest.json) |
| `R1LiteralReadAtFacts` | `a2013720cb3f16fd76fc5db794320df01d36805d8327c65150e5be5b931ce7dc` | `b` / 1.74 s / 3,584,292 KiB | 5 | [indexed prefix bundle](../evidence/lean-literal-indexed-prefix-20261015/source-manifest.json) |
| `R1LiteralIndexedPrefix` | `85152f1309f2157d24755851a8abc43f2648877028618b0ca93017a819f95045` | `a` / 1.49 s / 3,584,740 KiB | 4 | [indexed prefix bundle](../evidence/lean-literal-indexed-prefix-20261015/source-manifest.json) |
| `R1LiteralOpeningGood` | `89834499a9176e262e8b13d920240e9285956bb1ca2ec90f403029d4de983ee1` | `b` / 2.71 s / 3,631,828 KiB | 1 | [opening-good bundle](../evidence/lean-literal-opening-good-20261015/source-manifest.json) |
| `R1LiteralByteRunFacts` | `907f7c2e1ca22aa911479eeb7006008a6615ce22e7cd6d580b2a37c311905471` | `c` / 1.55 s / 3,616,620 KiB | 2 | [opening-good bundle](../evidence/lean-literal-opening-good-20261015/source-manifest.json) |
| `R1LiteralOpeningRunGood` | `a20f58693d29fb6dbbe260f17d23722a693298961d42bb7edf39c4c6e13a4626` | `a` / 1.97 s / 3,618,940 KiB | 2 | [opening-run-good bundle](../evidence/lean-literal-opening-run-good-20261015/source-manifest.json) |
| `R1LiteralQuerySample` | `891aac44d34a574ca790ad03ff56d6eeabfc62a26e2970822bb7a3c57bc7d118` | `b` / 1.68 s / 3,583,116 KiB | 2 | [opening-run-good bundle](../evidence/lean-literal-opening-run-good-20261015/source-manifest.json) |

All twelve targets used the pinned focused Lean runner with `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`, and `TasksMax=128`; each successful receipt reports zero swap. The report counts sum to 44.

`LiteralOpeningRunGood.good_of_transcript_read_noHit` lifts the prior reader-level result to an actual literal byte-transcript run: with at least 32 completed rounds, the successful opening reader and no-hit condition imply `Good`. The same module derives the row-27 gamma nonzero fact from the valid transcript/read condition; gamma nonzero is not an extra assumed premise. `LiteralQuerySample.valid_row31_success_decodes` checks that a successful row-31 q22 sample decodes to the required ordered, distinct, length-22, in-range query shape. The companion `scanOut_result_valid` establishes validity for outputs returned by the scan.

The checkpoint is about these deterministic opening and query facts. It does not prove that every accepted execution reaches the successful readers, close D3, establish full source/Pool correspondence, or complete the full security argument. In particular, the no-hit hypotheses remain explicit in the opening-good implication, and successful q22 decoding is not itself a proof that the complete protocol acceptance path supplies that success.

For the remaining all-bytes decoder interfaces, see [the all-bytes decoder reuse inventory](J1-ALL-BYTES-DECODER-REUSE-20261015.md). For the current privacy assumptions and formal boundary, see [the privacy reuse boundary](J5-PRIVACY-REUSE-BOUNDARY-20261015.md) and [the privacy rank path](../PRIVACY-RANK-PATH.md).

The [lead audit](../evidence/j1-opening-good-lead-review-20261015.json) independently verifies current sources, successful receipts and axiom logs, archive objects, and bundle checksums.
