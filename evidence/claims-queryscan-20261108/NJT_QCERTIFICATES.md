# QueryScan certificate register

Target not yet established. All four candidate rows await the primary NJT combined/raw/scan gate and the next ledger review; no ledger credit is claimed here.

| Row | Native certificate | Lean root | Exact domain |
|---|---|---|---|
| TX1:068 block_rank | NJT_QK004 actual proof_for_contract / QK005 inverted ensures; QK003/QK002 cell window pair | NJT_QLeaves.block_rank | All32 input bytes; arbitrary window0..7; all8 windows composed on the same output |
| TX1:070 query_words | Retained NGQ_K042/043 | NJT_QLeaves.query_words | All32 input bytes; arbitrary window0..7; actual block_rank executes natively |
| TX1:066 finish | Retained NGQ_K004/005 | NJT_QLeaves.finish | accepted_len<=22, draws<=64, arbitrary22-cell array; full Result including rejection |
| TX1:067 scan | Retained NHK_K034/035, complete NHK membership table, NHB_K030/031 and NHB_K050/051 | NJT_QReached.scan | Source default and every SAME-block carry; bounded, canonical and inactive-zero domains derived internally |
| TX1:069 queries_from_pairs | Retained NGQ_K046/047, K048/049, K058/059 plus prior rows | NJT_QPairs.reference (support only) | Exact8x32 blocks/advances, source default, first stop, fallback advance7; full Result. OPEN conservative child TX1:202 retained |

Cut transcriptions are P6/D188 option-A semantic-transport RECLASSIFICATION, not new trust and not trust removal. RankCut projects exactly `out[k]==expected`; WordsCut projects exactly the NGQ ordered LE/mask assertion; FinishCut preserves the original two scalar bounds and full Result cases. NJT_QScan.Cut projects the NHK_word_ref stop/length/draw/window assertions. The omitted log fields remain covered by the exact retained NHK certificate: membership count1 only on continuation, SAME prefix/candidate, post-increment draws, window-prefix cell. The implementation relation installs the CLOSED membership result at these arguments, then inducts forward. No successful child equation is retained as an external hypothesis.

The rank/model source is the existing coherent QueryScanConcreteWordsDecoder owner; NJT_QBase proves its complete Result without a successful-decode premise. The fresh native rank window executes the actual frozen block_rank. No new reference extraction or handwritten replacement extraction is claimed. Queries_from_pairs uses ReviewedTranscription-queries_from_pairs only for the Query31/NHK reference's Aeneas side and exactly its documented source-order8-block/word/finish scope; NHA outlined emission is corroboration, not original-body emission.

Standard operations (from_fn, array.map, IntoIter, from_le_bytes, prefix contains, Result constructors) use the existing pinned Aeneas/P7 side and native cuts under (au); no new dictionary or producer-association hypothesis is introduced. Native code executes std operations with the exact prescribed KMX patch. All caller-domain claims are explicit in NJT_QDomains and the default/prefix root. No new stub_verified shape, writable static, function-pointer-dependent Kani property, multiplication or new runtime trust is used.

NJT_QREUSE.json pins exact immutable receipt/control pairs and inherited source packets. Each new receipt pins selected Aeneas/library objects, source revision and source bytes. Frozen source remains4bb3b3f5; shipped files unchanged, so ELF pins are inherited, not rebuilt.

Actual-function NCO strengthening: QK004 verifies the frozen block_rank body against the literal identifier-renamed retained reference; pure modifies(). QK005 changes only the ensures to inequality and fails that postcondition. NJT_Q_REF_IDENTITY.json pins exact normalized-body identity; NJT_QReference.reference_correct pairs the reused emitted definition with rank. No stub_verified substitution is used, so no new interface-shape composition is claimed.
