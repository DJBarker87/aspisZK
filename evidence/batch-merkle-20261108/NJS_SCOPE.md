# NJS scope

Target not yet established. Baseline NJO: 463 CLOSED / 136 OPEN / 599; all 26 assigned occurrences OPEN. Full original obligations/caller clauses retained losslessly in NJS_BASELINE_ROWS.json.xz.

TX1/TX2 use the same non-generic helper bodies; digest helpers are generic over H and require the identical deployed SolanaDigest instantiation. Source-body identity alone is not monomorphization evidence; each occurrence must be checked independently against its clauses. No duplicate native certificate is planned when the deployed instantiation matches.

| Row | Frozen body SHA256 | Cohort named by inventory | Direct callees/status |
|---|---|---|---|
| TX1:065 parent_with_digest | 4ab7b85f08e1f3bb587e32016edc6d56994fc11650cd12bac1462077e19990bd | no cohort counterpart named; resolve canonical emitted definition | digest:CLOSED |
| TX1:077 private_leaf_hash_with_digest | 13bc91af598ba8984ba3400e13461d4494e4432867461732633d4115eb11b782 | no cohort counterpart named; resolve canonical emitted definition | digest:CLOSED |
| TX1:078 batch_key_at | 9375a4d3a90b700556a0791c63a09028877e7efc3a498a5e5ae80caa95186391 | no cohort counterpart named; resolve canonical emitted definition | none |
| TX1:079 batch_keys | 9184bd058bf5b12f9e29468332ccc284553ead3e1165c6e8f39967ba49173174 | AspisR1.Port4B_KeyInstall.keyArray | none |
| TX1:080 batch_leaf | 7e28698baab02eff1799ae0e2bb6c1b2465126f533f12dd2c1a19ee79745439f | AspisR1.Port4B_LeafCode.codeFor | private_leaf_hash_with_digest:OPEN |
| TX1:081 batch_merkle | 5d3185fb3c312df117d4ac648233fa5058c852938374a192811445e2c255559d | AspisR1.Port3_NativeBatchBody.verifier.candidate.batch_merkle | batch_merkle_values:OPEN |
| TX1:082 batch_merkle_values | f09046e56911e28a71281efdd6d4ff94c2e83bc9d603bba8904e41e130e61936 | AspisR1.Port3_NativeBatchBody.verifier.candidate.batch_merkle_values | batch_tree:OPEN |
| TX1:083 batch_tree | 3feed1a7f0bdd8ea5089b0bc974fe5d61bb041e0c24d378ac6e40e4fd6a35342 | AspisR1.Port3_NativeBatchBody.verifier.candidate.batch_tree | batch_key_at:OPEN, batch_keys:OPEN, batch_leaf:OPEN, opening:CLOSED, same_batch_index:OPEN, same_batch_leaf:OPEN, slot:OPEN, sort_batch_keys:OPEN, node_count:CLOSED, verify_in_place:OPEN |
| TX1:084 canonical_scan | 66bbf3452338ab0aa3d5f779c55c38f84a0ff42261abc69d199d10dd18cd61d0 | Op4P_Extract.Op4P_reference.canonical_scan | from_le_bytes:CLOSED, from_le_bytes:CLOSED, opening:CLOSED, check_values:CLOSED, echeck:OPEN |
| TX1:086 parse_shape | 41d660ce759042d8296dd5122654b5af6b1897a98ecc8f5a2d79630760b2a4fe | Op3I_Source.verifier.candidate.parse_shape | tag:CLOSED |
| TX1:090 same_batch_index | 58f76e0bd7f39fed3b37325b66e88522992873f4aebfa08d35220d83dcceed58 | AspisR1.Port3_BatchStd.sameIndex | none |
| TX1:091 same_batch_leaf | ab9ddbf6e34161f92525212249859d894b23d9574f009855e1bdac992a44f9f8 | AspisR1.Port3_BatchStd.sameLeaf | none |
| TX1:092 slot | fc2fcc8a5aa52bdb44b9b379c8274a7847de79859cad3f7902edcde05a2f39a5 | AspisR1.Port4B_SlotInstall.nodeSlot | slot_offset:CLOSED |
| TX1:093 sort_batch_keys | cff533add02fd02df332860e6d81c3dccd32783b5757a2967b75de797938a04d | AspisR1.Port4B_SortInstall.key_stream | batch_key_at:OPEN |
| TX2:049 private_leaf_hash_with_digest | 13bc91af598ba8984ba3400e13461d4494e4432867461732633d4115eb11b782 | no cohort counterpart named; resolve canonical emitted definition | digest:CLOSED |
| TX2:050 batch_key_at | 9375a4d3a90b700556a0791c63a09028877e7efc3a498a5e5ae80caa95186391 | no cohort counterpart named; resolve canonical emitted definition | none |
| TX2:051 batch_keys | 9184bd058bf5b12f9e29468332ccc284553ead3e1165c6e8f39967ba49173174 | AspisR1.Port4B_KeyInstall.keyArray | none |
| TX2:052 batch_leaf | 7e28698baab02eff1799ae0e2bb6c1b2465126f533f12dd2c1a19ee79745439f | AspisR1.Port4B_LeafCode.codeFor | private_leaf_hash_with_digest:OPEN |
| TX2:053 batch_merkle | 5d3185fb3c312df117d4ac648233fa5058c852938374a192811445e2c255559d | AspisR1.Port3_NativeBatchBody.verifier.candidate.batch_merkle | batch_merkle_values:OPEN |
| TX2:054 batch_merkle_values | f09046e56911e28a71281efdd6d4ff94c2e83bc9d603bba8904e41e130e61936 | AspisR1.Port3_NativeBatchBody.verifier.candidate.batch_merkle_values | batch_tree:OPEN |
| TX2:055 batch_tree | 3feed1a7f0bdd8ea5089b0bc974fe5d61bb041e0c24d378ac6e40e4fd6a35342 | AspisR1.Port3_NativeBatchBody.verifier.candidate.batch_tree | batch_key_at:OPEN, batch_keys:OPEN, batch_leaf:OPEN, opening:CLOSED, same_batch_index:OPEN, same_batch_leaf:OPEN, slot:OPEN, sort_batch_keys:OPEN, node_count:CLOSED, verify_in_place:OPEN |
| TX2:057 parse_shape | 41d660ce759042d8296dd5122654b5af6b1897a98ecc8f5a2d79630760b2a4fe | Op3I_Source.verifier.candidate.parse_shape | tag:CLOSED |
| TX2:060 same_batch_index | 58f76e0bd7f39fed3b37325b66e88522992873f4aebfa08d35220d83dcceed58 | AspisR1.Port3_BatchStd.sameIndex | none |
| TX2:061 same_batch_leaf | ab9ddbf6e34161f92525212249859d894b23d9574f009855e1bdac992a44f9f8 | AspisR1.Port3_BatchStd.sameLeaf | none |
| TX2:062 slot | fc2fcc8a5aa52bdb44b9b379c8274a7847de79859cad3f7902edcde05a2f39a5 | AspisR1.Port4B_SlotInstall.nodeSlot | slot_offset:CLOSED |
| TX2:063 sort_batch_keys | cff533add02fd02df332860e6d81c3dccd32783b5757a2967b75de797938a04d | AspisR1.Port4B_SortInstall.key_stream | batch_key_at:OPEN |

Bottom-up order: (1) batch_key_at, same_batch_index, same_batch_leaf; digest grammar leaves in parallel dependency order; (2) slot over CLOSED slot_offset, parse_shape over CLOSED tag plus rule-3 any; (3) batch_keys one native iteration + Lean induction, sort_batch_keys swap/inner/outer induction; (4) batch_leaf over private leaf; (5) batch_tree over these and opening/node_count, with verify_in_place consumed only after sibling merge; (6) batch_merkle_values then batch_merkle. canonical_scan reuses NJC/NJJ partial cuts and existing CLOSED field decoders; its final history relation is separate.

Potential domain finding: private_leaf existing native PacketDomain caps values at416, while batch_leaf tree0 passes480 bytes. Widen via selected-window/copy frame, never assume480<=416. Parent eight-way digest leaf may be a conservative alternative under binary multiproof; retain until resolved from frozen call structure.

No root may retain a child-result/endpoint or arbitrary Ops dictionary hypothesis; cut transcriptions are authored under(ai)(5), CLOSED children instantiated under(aq)/(aq)(5), complete Results and rejection prefixes retained.
