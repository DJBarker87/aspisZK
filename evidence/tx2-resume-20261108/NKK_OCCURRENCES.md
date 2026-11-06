# NKK resume occurrence inventory

TX2:124 OPEN; target not yet established. The table lists every top-level NJU_ResumeObserved Event in source order on the maximal entered path. Error/abort prefixes stop before all later rows. Nested semantic and weight reads are enumerated below, not silently treated as single Reader occurrences.

| # | Site / SAME arguments | Native cut or CLOSED child | Frame/domain |
|---|---|---|---|
| 1 | headerAny: bytes[11..16], initial iterator | NJJ_K009/010 + NJJ_Any.installed/frame; NKK_K028/029/030 | checkpoint/proof/public immutable; all unrelated state retained; S2 header guard, actual length checked before indexing |
| 2 | proofDigest: [proof] | NJJ_K038/039 checksum; NKK_K042/046/047/050 | checkpoint/proof/public immutable; all unrelated state retained; ordered count and reply unchanged; proof57607; public length <=1880; checkpoint1768; runtime digest value only |
| 3 | publicDigest: [public] | NJJ_K038/039 checksum; NKK_K034/035 | checkpoint/proof/public immutable; all unrelated state retained; ordered count and reply unchanged; proof57607; public length <=1880; checkpoint1768; runtime digest value only |
| 4 | checkpointDigest: [literal22,bytes[0..1736]] | NJJ_K038/039 checksum; NKK_K036/043/044 | checkpoint/proof/public immutable; all unrelated state retained; ordered count and reply unchanged; proof57607; public length <=1880; checkpoint1768; runtime digest value only |
| 5 | rawRoot0: raw32 cursor 80 | NJJ_K042/043; NJZ_Readers.raw_cut; NKK_K009/010/011 + NKK_RawPrefix/RawSlots | checkpoint/proof/public immutable; all unrelated state retained; cursor +32; S2 checkpoint backing 1768 |
| 6 | rawRoot1: raw32 cursor 112 | NJJ_K042/043; NJZ_Readers.raw_cut; NKK_K009/010/011 + NKK_RawPrefix/RawSlots | checkpoint/proof/public immutable; all unrelated state retained; cursor +32; S2 checkpoint backing 1768 |
| 7 | rawRoot2: raw32 cursor 144 | NJJ_K042/043; NJZ_Readers.raw_cut; NKK_K009/010/011 + NKK_RawPrefix/RawSlots | checkpoint/proof/public immutable; all unrelated state retained; cursor +32; S2 checkpoint backing 1768 |
| 8 | gammaAlpha0: e cursor 176 | NJJ_K044/045; NJZ_Readers.e_source/e_reference; NKK_K013/014/015 + NKK_FieldAssociation/FieldDomain | checkpoint/proof/public immutable; all unrelated state retained; cursor +32 even decoder Err; S2 checkpoint backing 1768 |
| 9 | gammaAlpha1: e cursor 208 | NJJ_K044/045; NJZ_Readers.e_source/e_reference; NKK_K013/014/015 + NKK_FieldAssociation/FieldDomain | checkpoint/proof/public immutable; all unrelated state retained; cursor +32 even decoder Err; S2 checkpoint backing 1768 |
| 10 | gammaAlpha2: e cursor 240 | NJJ_K044/045; NJZ_Readers.e_source/e_reference; NKK_K013/014/015 + NKK_FieldAssociation/FieldDomain | checkpoint/proof/public immutable; all unrelated state retained; cursor +32 even decoder Err; S2 checkpoint backing 1768 |
| 11 | gammaAlpha3: e cursor 272 | NJJ_K044/045; NJZ_Readers.e_source/e_reference; NKK_K013/014/015 + NKK_FieldAssociation/FieldDomain | checkpoint/proof/public immutable; all unrelated state retained; cursor +32 even decoder Err; S2 checkpoint backing 1768 |
| 12 | rho: k cursor304 | NJJ_K046/047; NJZ_Readers.k_source/k_reference; NKK_K013/014/015 + NKK_FieldAssociation/FieldDomain | checkpoint/proof/public immutable; all unrelated state retained; cursor+16 even decoder Err; S2 checkpoint backing 1768 |
| 13 | query0: raw4 cursor 320 | NJJ_K040/041; NJZ_Readers.raw_cut; NKK_K003/004 + NKK_QueryStage.stage8 | checkpoint/proof/public immutable; all unrelated state retained; cursor+4; from_le_bytes same array; S2 checkpoint backing 1768 |
| 14 | query1: raw4 cursor 324 | NJJ_K040/041; NJZ_Readers.raw_cut; NKK_K003/004 + NKK_QueryStage.stage8 | checkpoint/proof/public immutable; all unrelated state retained; cursor+4; from_le_bytes same array; S2 checkpoint backing 1768 |
| 15 | query2: raw4 cursor 328 | NJJ_K040/041; NJZ_Readers.raw_cut; NKK_K003/004 + NKK_QueryStage.stage8 | checkpoint/proof/public immutable; all unrelated state retained; cursor+4; from_le_bytes same array; S2 checkpoint backing 1768 |
| 16 | query3: raw4 cursor 332 | NJJ_K040/041; NJZ_Readers.raw_cut; NKK_K003/004 + NKK_QueryStage.stage8 | checkpoint/proof/public immutable; all unrelated state retained; cursor+4; from_le_bytes same array; S2 checkpoint backing 1768 |
| 17 | query4: raw4 cursor 336 | NJJ_K040/041; NJZ_Readers.raw_cut; NKK_K003/004 + NKK_QueryStage.stage8 | checkpoint/proof/public immutable; all unrelated state retained; cursor+4; from_le_bytes same array; S2 checkpoint backing 1768 |
| 18 | query5: raw4 cursor 340 | NJJ_K040/041; NJZ_Readers.raw_cut; NKK_K003/004 + NKK_QueryStage.stage8 | checkpoint/proof/public immutable; all unrelated state retained; cursor+4; from_le_bytes same array; S2 checkpoint backing 1768 |
| 19 | query6: raw4 cursor 344 | NJJ_K040/041; NJZ_Readers.raw_cut; NKK_K003/004 + NKK_QueryStage.stage8 | checkpoint/proof/public immutable; all unrelated state retained; cursor+4; from_le_bytes same array; S2 checkpoint backing 1768 |
| 20 | query7: raw4 cursor 348 | NJJ_K040/041; NJZ_Readers.raw_cut; NKK_K003/004 + NKK_QueryStage.stage8 | checkpoint/proof/public immutable; all unrelated state retained; cursor+4; from_le_bytes same array; S2 checkpoint backing 1768 |
| 21 | query8: raw4 cursor 352 | NJJ_K040/041; NJZ_Readers.raw_cut; NKK_K003/004 + NKK_QueryStage.stage8 | checkpoint/proof/public immutable; all unrelated state retained; cursor+4; from_le_bytes same array; S2 checkpoint backing 1768 |
| 22 | query9: raw4 cursor 356 | NJJ_K040/041; NJZ_Readers.raw_cut; NKK_K003/004 + NKK_QueryStage.stage8 | checkpoint/proof/public immutable; all unrelated state retained; cursor+4; from_le_bytes same array; S2 checkpoint backing 1768 |
| 23 | query10: raw4 cursor 360 | NJJ_K040/041; NJZ_Readers.raw_cut; NKK_K003/004 + NKK_QueryStage.stage8 | checkpoint/proof/public immutable; all unrelated state retained; cursor+4; from_le_bytes same array; S2 checkpoint backing 1768 |
| 24 | query11: raw4 cursor 364 | NJJ_K040/041; NJZ_Readers.raw_cut; NKK_K003/004 + NKK_QueryStage.stage8 | checkpoint/proof/public immutable; all unrelated state retained; cursor+4; from_le_bytes same array; S2 checkpoint backing 1768 |
| 25 | query12: raw4 cursor 368 | NJJ_K040/041; NJZ_Readers.raw_cut; NKK_K003/004 + NKK_QueryStage.stage8 | checkpoint/proof/public immutable; all unrelated state retained; cursor+4; from_le_bytes same array; S2 checkpoint backing 1768 |
| 26 | query13: raw4 cursor 372 | NJJ_K040/041; NJZ_Readers.raw_cut; NKK_K003/004 + NKK_QueryStage.stage8 | checkpoint/proof/public immutable; all unrelated state retained; cursor+4; from_le_bytes same array; S2 checkpoint backing 1768 |
| 27 | query14: raw4 cursor 376 | NJJ_K040/041; NJZ_Readers.raw_cut; NKK_K003/004 + NKK_QueryStage.stage8 | checkpoint/proof/public immutable; all unrelated state retained; cursor+4; from_le_bytes same array; S2 checkpoint backing 1768 |
| 28 | query15: raw4 cursor 380 | NJJ_K040/041; NJZ_Readers.raw_cut; NKK_K003/004 + NKK_QueryStage.stage8 | checkpoint/proof/public immutable; all unrelated state retained; cursor+4; from_le_bytes same array; S2 checkpoint backing 1768 |
| 29 | query16: raw4 cursor 384 | NJJ_K040/041; NJZ_Readers.raw_cut; NKK_K006/007/008 + NKK_QueryStage.stage6 | checkpoint/proof/public immutable; all unrelated state retained; cursor+4; from_le_bytes same array; S2 checkpoint backing 1768 |
| 30 | query17: raw4 cursor 388 | NJJ_K040/041; NJZ_Readers.raw_cut; NKK_K006/007/008 + NKK_QueryStage.stage6 | checkpoint/proof/public immutable; all unrelated state retained; cursor+4; from_le_bytes same array; S2 checkpoint backing 1768 |
| 31 | query18: raw4 cursor 392 | NJJ_K040/041; NJZ_Readers.raw_cut; NKK_K006/007/008 + NKK_QueryStage.stage6 | checkpoint/proof/public immutable; all unrelated state retained; cursor+4; from_le_bytes same array; S2 checkpoint backing 1768 |
| 32 | query19: raw4 cursor 396 | NJJ_K040/041; NJZ_Readers.raw_cut; NKK_K006/007/008 + NKK_QueryStage.stage6 | checkpoint/proof/public immutable; all unrelated state retained; cursor+4; from_le_bytes same array; S2 checkpoint backing 1768 |
| 33 | query20: raw4 cursor 400 | NJJ_K040/041; NJZ_Readers.raw_cut; NKK_K006/007/008 + NKK_QueryStage.stage6 | checkpoint/proof/public immutable; all unrelated state retained; cursor+4; from_le_bytes same array; S2 checkpoint backing 1768 |
| 34 | query21: raw4 cursor 404 | NJJ_K040/041; NJZ_Readers.raw_cut; NKK_K006/007/008 + NKK_QueryStage.stage6 | checkpoint/proof/public immutable; all unrelated state retained; cursor+4; from_le_bytes same array; S2 checkpoint backing 1768 |
| 35 | validate: same assembled query22 | NJC_K033/034/036/037; NJZ_Validator.source; CLOSED TX2:126 | checkpoint/proof/public immutable; all unrelated state retained; exact Error; no later event after Err; all U32 arrays22 |
| 36 | semantic: bytes, cursor408 | TX2:121 NJZ_CheckpointReaders.semantic; NKK_K025/026/027 | checkpoint/proof/public immutable; all unrelated state retained; all10 K Results; returned cursor; SAME1768 / cursor408; nested reads16 at408+16*i (i<10) |
| 37 | z0: k cursor 568 | NJJ_K050/051; NJZ_Readers.k_source/k_reference; NKK_K016/017/018 + NKK_ZStage.source_eq_model | checkpoint/proof/public immutable; all unrelated state retained; cursor+16 even decoder Err; S2 checkpoint backing 1768 |
| 38 | z1: k cursor 584 | NJJ_K050/051; NJZ_Readers.k_source/k_reference; NKK_K016/017/018 + NKK_ZStage.source_eq_model | checkpoint/proof/public immutable; all unrelated state retained; cursor+16 even decoder Err; S2 checkpoint backing 1768 |
| 39 | z2: k cursor 600 | NJJ_K050/051; NJZ_Readers.k_source/k_reference; NKK_K016/017/018 + NKK_ZStage.source_eq_model | checkpoint/proof/public immutable; all unrelated state retained; cursor+16 even decoder Err; S2 checkpoint backing 1768 |
| 40 | z3: k cursor 616 | NJJ_K050/051; NJZ_Readers.k_source/k_reference; NKK_K016/017/018 + NKK_ZStage.source_eq_model | checkpoint/proof/public immutable; all unrelated state retained; cursor+16 even decoder Err; S2 checkpoint backing 1768 |
| 41 | claimRhs0: e cursor 632 | NJJ_K052/053; NJZ_Readers.e_source/e_reference; NKK_K016/017/018 + NKK_ZStage.source_eq_model | checkpoint/proof/public immutable; all unrelated state retained; cursor+32 even decoder Err; S2 checkpoint backing 1768 |
| 42 | claimRhs1: e cursor 664 | NJJ_K052/053; NJZ_Readers.e_source/e_reference; NKK_K016/017/018 + NKK_ZStage.source_eq_model | checkpoint/proof/public immutable; all unrelated state retained; cursor+32 even decoder Err; S2 checkpoint backing 1768 |
| 43 | power: k cursor696 | NJJ_K054/055; NJZ_Readers.k_source/k_reference; NKK_K016/017/018 + NKK_ZStage.source_eq_model | checkpoint/proof/public immutable; all unrelated state retained; cursor+16 even decoder Err; S2 checkpoint backing 1768 |
| 44 | filled: n64, ZERO K, SAME Reservation | NJJ_K066/067/068/069; NJR_ReservationSites.resume_filled; NKK_AllocationBind.rejected | checkpoint/proof/public immutable; all unrelated state retained; full owned Vec; allocation Err maps Allocation; both Reservation arms; actual allocator event at this site |
| 45 | weights: bytes,cursor712,SAME owned Vec64 | TX2:122 NJZ_CheckpointReaders.weights + NJR_K042/043/044/045; NKK_SectionFrames.weights | checkpoint/proof/public immutable; all unrelated state retained; all64 payloads; full Err/drop; length/capacity/allocation; SAME1768 / cursor712 / owned64; nested reads16 at712+16*i (i<64) |

## Nested Reader occurrences

| Parent | Index | N / cursor / backing | Cut | Frame |
|---|---|---|---|---|
| semantic | 0 | 16 / 408 / SAME1768 | NJJ_K048/049; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| semantic | 1 | 16 / 424 / SAME1768 | NJJ_K048/049; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| semantic | 2 | 16 / 440 / SAME1768 | NJJ_K048/049; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| semantic | 3 | 16 / 456 / SAME1768 | NJJ_K048/049; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| semantic | 4 | 16 / 472 / SAME1768 | NJJ_K048/049; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| semantic | 5 | 16 / 488 / SAME1768 | NJJ_K048/049; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| semantic | 6 | 16 / 504 / SAME1768 | NJJ_K048/049; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| semantic | 7 | 16 / 520 / SAME1768 | NJJ_K048/049; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| semantic | 8 | 16 / 536 / SAME1768 | NJJ_K048/049; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| semantic | 9 | 16 / 552 / SAME1768 | NJJ_K048/049; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 0 | 16 / 712 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 1 | 16 / 728 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 2 | 16 / 744 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 3 | 16 / 760 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 4 | 16 / 776 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 5 | 16 / 792 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 6 | 16 / 808 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 7 | 16 / 824 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 8 | 16 / 840 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 9 | 16 / 856 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 10 | 16 / 872 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 11 | 16 / 888 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 12 | 16 / 904 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 13 | 16 / 920 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 14 | 16 / 936 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 15 | 16 / 952 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 16 | 16 / 968 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 17 | 16 / 984 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 18 | 16 / 1000 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 19 | 16 / 1016 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 20 | 16 / 1032 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 21 | 16 / 1048 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 22 | 16 / 1064 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 23 | 16 / 1080 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 24 | 16 / 1096 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 25 | 16 / 1112 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 26 | 16 / 1128 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 27 | 16 / 1144 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 28 | 16 / 1160 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 29 | 16 / 1176 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 30 | 16 / 1192 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 31 | 16 / 1208 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 32 | 16 / 1224 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 33 | 16 / 1240 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 34 | 16 / 1256 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 35 | 16 / 1272 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 36 | 16 / 1288 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 37 | 16 / 1304 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 38 | 16 / 1320 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 39 | 16 / 1336 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 40 | 16 / 1352 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 41 | 16 / 1368 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 42 | 16 / 1384 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 43 | 16 / 1400 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 44 | 16 / 1416 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 45 | 16 / 1432 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 46 | 16 / 1448 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 47 | 16 / 1464 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 48 | 16 / 1480 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 49 | 16 / 1496 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 50 | 16 / 1512 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 51 | 16 / 1528 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 52 | 16 / 1544 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 53 | 16 / 1560 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 54 | 16 / 1576 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 55 | 16 / 1592 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 56 | 16 / 1608 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 57 | 16 / 1624 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 58 | 16 / 1640 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 59 | 16 / 1656 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 60 | 16 / 1672 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 61 | 16 / 1688 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 62 | 16 / 1704 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |
| weights | 63 | 16 / 1720 / SAME1768 | NJJ_K056/057; NJR_K042/043/044/045; NJZ_Readers.k_source | backing immutable; cursor+16; complete canonicality Err; weights additionally owned Vec/store/drop |

## Parent-only sites not represented by Event

- Header length, magic/tag/next/flag/reserved guards: NJJ_K009/010; actual length test dominates every header slice. No assertion about arbitrary short slice indexing is imported.
- Digest comparisons/short-circuit: NJJ_K038/039 checks prefix count and exact argument descriptors. Its proof/public domain must be established by the caller or generalized; it is not silently universal.
- Query array and from_le_bytes: native query_word and constructors plus pinned std/alloc interpretation (au); no new child row.
- Reader initialization/cursor writeback: raw source-site cuts and semantic/weights SAME returned cursor; full backing equality, never address-implies-payload.
- Final cursor comparison: NJJ_K058/059 tail_guard at1736, with SAME returned Vec required for an owned error exit.
- Prepared Box: NJJ_K060/061/062, complete fields and allocation; returning/abort scope under (aa), no allocation-success premise.
- Accumulator: NJJ_K063/064/065, SAME weights allocation/length/capacity and all fields.
- Cleanup: early parser/validator errors precede filled; weights-child Err/drop is NJR_ReaderCut/NJR_WeightFailure. After filled, tail mismatch drops the returned weights; Box allocation abort is an (aa)/(an) prefix. The actual owned parent association at these two sites still needs explicit installation in the native fold. NJU Event alone does not express that ownership state.

No raw Reader occurrence falls outside N=4/16/32 on the1768-byte backing. The parsers receive16/32-byte windows through CLOSED codec rows; these are not extra whole-backing Reader calls. Source log has45 maximal top-level events plus74 nested scalar reads. No closure credit follows from this enumeration.

## Final disposition

The new NKK component column is cross-referenced in NKK_NATIVE_CERTIFICATES.json; each native component has a matched failing control, including the complete proof frame via the calibrated contract shape. NKK_OCCURRENCES.json marks the full native parent association OPEN for every event. Source equality, successful child clauses and independently checked components do not install that parent association. The ordered digest source chain and allocation rejection continuation are additionally NKK_DigestChain and NKK_AllocationBind.

No additional Reader width/backing window was found: all primitive reads are N4/16/32 on the actual1768 backing. All74 nested reads remain explicitly enumerated above. Every actual parser invocation has its own complete Result, cursor/frame and exact-error clause; decoder canonicality is derived on success by NKK_DecoderDomain, never assumed at the root. Remaining SAME-argument installation and owned cleanup obligations are listed member-by-member in NKK_REMAINING.md. No composed row is CLOSED.
