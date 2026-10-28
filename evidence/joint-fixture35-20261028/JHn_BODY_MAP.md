# Checkpoint body byte map

Offsets are zero based; ranges are half open. The body is checkpoint[0:1736]; checksum[1736:1768] is outside it. All theorem names below are in AspisR1. The field constants are linked to actual preparation/query/flush operands by JHl_KnownFields.source and JHm_JointSkeleton.selected.

The missing 80 bytes are **header16 + proof digest32 + physical public digest32**. They were already covered by the named retained-range theorems below, not part of the 1624+32 field-byte count. Digest range selection alone is not a proof that an actual digest call returns those bytes; that is a separate composition obligation.

| Offset | Length | Field | Exact retained-range identity theorem |
|---:|---:|---|---|
| 0 | 16 | magic, variant, next, flags/reserved | `JFq_AuthBytes.first16; JHe_CurrentWriterImage.header` |
| 16 | 32 | proof digest | `JFq_AuthBytes.proofHash_selected (JFq_Range.segment 16 32)` |
| 48 | 32 | physical public digest | `JFq_AuthBytes.publicHash_selected (JFq_Range.segment 48 32)` |
| 80 | 32 | state | `JFq_State.selected` |
| 112 | 32 | root0 | `JFq_Root0.selected` |
| 144 | 32 | root1 | `JFq_Root1.selected` |
| 176 | 32 | gamma | `JFq_Gamma.selected` |
| 208 | 32 | kappa | `JFq_Kappa.selected` |
| 240 | 32 | alpha0 | `JFq_Alpha0.selected` |
| 272 | 32 | alpha1 | `JFq_Alpha1.selected` |
| 304 | 16 | rho | `JFq_Rho.selected` |
| 320 | 4 | query0 | `JFq_QueryWords.select0` |
| 324 | 4 | query1 | `JFq_QueryWords.select1` |
| 328 | 4 | query2 | `JFq_QueryWords.select2` |
| 332 | 4 | query3 | `JFq_QueryWords.select3` |
| 336 | 4 | query4 | `JFq_QueryWords.select4` |
| 340 | 4 | query5 | `JFq_QueryWords.select5` |
| 344 | 4 | query6 | `JFq_QueryWords.select6` |
| 348 | 4 | query7 | `JFq_QueryWords.select7` |
| 352 | 4 | query8 | `JFq_QueryWords.select8` |
| 356 | 4 | query9 | `JFq_QueryWords.select9` |
| 360 | 4 | query10 | `JFq_QueryWords.select10` |
| 364 | 4 | query11 | `JFq_QueryWords.select11` |
| 368 | 4 | query12 | `JFq_QueryWords.select12` |
| 372 | 4 | query13 | `JFq_QueryWords.select13` |
| 376 | 4 | query14 | `JFq_QueryWords.select14` |
| 380 | 4 | query15 | `JFq_QueryWords.select15` |
| 384 | 4 | query16 | `JFq_QueryWords.select16` |
| 388 | 4 | query17 | `JFq_QueryWords.select17` |
| 392 | 4 | query18 | `JFq_QueryWords.select18` |
| 396 | 4 | query19 | `JFq_QueryWords.select19` |
| 400 | 4 | query20 | `JFq_QueryWords.select20` |
| 404 | 4 | query21 | `JFq_QueryWords.select21` |
| 408 | 16 | semantic_alpha0 | `JFq_Sem00.selected` |
| 424 | 16 | semantic_alpha1 | `JFq_Sem01.selected` |
| 440 | 16 | semantic_alpha2 | `JFq_Sem02.selected` |
| 456 | 16 | semantic_alpha3 | `JFq_Sem03.selected` |
| 472 | 16 | semantic_alpha4 | `JFq_Sem04.selected` |
| 488 | 16 | semantic_alpha5 | `JFq_Sem05.selected` |
| 504 | 16 | semantic_alpha6 | `JFq_Sem06.selected` |
| 520 | 16 | semantic_alpha7 | `JFq_Sem07.selected` |
| 536 | 16 | semantic_alpha8 | `JFq_Sem08.selected` |
| 552 | 16 | semantic_alpha9 | `JFq_Sem09.selected` |
| 568 | 16 | z coordinate0 | `JFq_Z0.selected` |
| 584 | 16 | z coordinate1 | `JFq_Z1.selected` |
| 600 | 16 | z coordinate2 | `JFq_Z2.selected` |
| 616 | 16 | z coordinate3 | `JFq_Z3.selected` |
| 632 | 32 | claim | `JFq_Claim.selected; JHm_JointSkeleton.selected` |
| 664 | 32 | rhs | `JFq_Rhs.selected` |
| 696 | 16 | power | `JFq_Power.selected` |
| 712 | 1024 | 64 weights | `JHl_WeightOutput.source (actual serialized weights equal this checkpoint range)` |

Total: **1736 bytes**, contiguous and non-overlapping. Header flags occupy offsets10..15; magic0..7, variant8, next9.
