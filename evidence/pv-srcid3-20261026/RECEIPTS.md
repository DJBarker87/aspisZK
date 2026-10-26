# Recorded receipts

Resume through 2026-10-26 21:47 UTC: no new host run or local Lean compile.
The restoration flag is absent (host-gate-checks.jsonl). No compile receipt
is invented for draft/static inventory work. Lean 37 and Kani 8 remain;
Env-J next ID 27400. The following tables retain historical receipts.

Exact source hashes, dependency objects and complete #print axioms are in attempts.jsonl.
This table is a rendering of existing evidence, not a final kernel replay.

## Lean

| ID | Target | Exit | Wall | Peak RSS KiB | Swap | Revision | Axioms |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 25301 | R1Z/PV_Src_CheckedEncoding | 0 | 0:01.83 | 4109048 | 0 | 07871677ad | standard only |
| 25302 | R1Z/PV_Src_CheckedValidation | 0 | 0:01.85 | 4105912 | 0 | 14e6cace50 | standard only |
| 25303 | R1Z/PV_Src_CheckedVariants | 0 | 0:01.97 | 4096656 | 0 | 14e6cace50 | standard only |
| 25304 | R1Z/PV_Src_RecordDynamic | 0 | 0:01.79 | 4105924 | 0 | 14e6cace50 | standard only |
| 25305 | R1Z/PV_Src_CanonicalRequest | 0 | 0:02.02 | 4108608 | 0 | 14e6cace50 | standard only |
| 25306 | R1Z/PV_Src_CheckedCanonical | 0 | 0:01.81 | 4108160 | 0 | 14e6cace50 | standard only |
| 25307 | R1Z/PV_Src_CheckedFixtures | 0 | 0:01.90 | 4220288 | 0 | 14e6cace50 | standard only |
| 25308 | R1Z/PV_Src_SelectedFour | 0 | 0:01.85 | 4116828 | 0 | 14e6cace50 | standard only |
| 25309 | R1Z/PV_Src_SelectedConsumer | 1 | 0:02.21 | 4217888 | 0 | 14e6cace50 | FAILED — not accepted |
| 25310 | R1Z/PV_Src_SelectedConsumer | 0 | 0:02.31 | 4239600 | 0 | 97ffb27f22 | standard only |
| 25311 | R1Z/PV_Src_ReturnedSnapshot | 0 | 0:02.86 | 4145708 | 0 | 3ca2574818 | standard only |
| 25312 | R1Z/PV_Src_RecordDynamicResult | 0 | 0:01.81 | 4098204 | 0 | 3ca2574818 | standard only |
| 25313 | R1Z/PV_Src_PublicHeader | 1 | 0:01.85 | 4096364 | 0 | 3ca2574818 | FAILED — not accepted |
| 25314 | R1Z/PV_Src_PublicHeader | 0 | 0:01.99 | 4118664 | 0 | 3ca2574818 | standard only |
| 25315 | R1Z/PV_Src_PublicParts | 1 | 0:01.80 | 4092376 | 0 | 3ca2574818 | FAILED — not accepted |
| 25316 | R1Z/PV_Src_BanksTotal | 0 | 0:01.74 | 4109632 | 0 | 3ca2574818 | standard only |
| 25317 | R1Z/PV_Src_PublicParts | 0 | 0:01.85 | 4115368 | 0 | 3ca2574818 | standard only |
| 25318 | R1Z/PV_Src_CheckedPipeline | 0 | 0:01.89 | 4223744 | 0 | 3ca2574818 | standard only |
| 25319 | R1Z/PV_Src_ExternalReference | 0 | 0:01.27 | 2591616 | 0 | 92f7b85c5c | standard only |
| 25320 | R1Z/PV_Src_ExternalReduce | 1 | 0:01.91 | 4081964 | 0 | 92f7b85c5c | FAILED — not accepted |
| 25321 | R1Z/PV_Src_AdmissionArray | 1 | 0:01.81 | 4077368 | 0 | 92f7b85c5c | FAILED — not accepted |
| 25322 | R1Z/PV_Src_ExternalReduce | 0 | 0:02.14 | 4102472 | 0 | 92f7b85c5c | standard only |
| 25323 | R1Z/PV_Src_AdmissionArray | 0 | 0:01.88 | 4096996 | 0 | 92f7b85c5c | standard only |
| 25324 | R1Z/PV_Src_ScalarFold | 0 | 0:01.94 | 4102112 | 0 | 92f7b85c5c | standard only |
| 25325 | R1Z/PV_Src_ScalarReduce | 1 | 0:01.92 | 4089044 | 0 | 92f7b85c5c | FAILED — not accepted |
| 25327 | R1Z/PV_Src_ScalarReduce | 0 | 0:01.85 | 4109612 | 0 | ef310fbcad | standard only |
| 25329 | R1Z/PV_Src_AdmissionDigest | 0 | 0:01.93 | 4098424 | 0 | ef310fbcad | standard only |
| 25330 | R1Z/PV_Src_AdmissionScalar | 1 | 0:01.87 | 4087664 | 0 | ef310fbcad | FAILED — not accepted |
| 25331 | R1Z/PV_Src_ExternalBlocks | 0 | 0:02.37 | 4107856 | 0 | ef310fbcad | standard only |
| 25332 | R1Z/PV_Src_AdmissionScalar | 1 | 0:02.34 | 4076596 | 0 | ef310fbcad | FAILED — not accepted |
| 25334 | R1Z/PV_Src_AdmissionScalar | 0 | 0:02.04 | 4109248 | 0 | 597a70c88c | standard only |
| 25335 | R1Z/PV_Src_ExternalSums | 0 | 0:02.11 | 4107652 | 0 | 597a70c88c | standard only |
| 25336 | R1Z/PV_Src_AdmissionOccupiedScan | 1 | 0:01.78 | 4086376 | 0 | 597a70c88c | FAILED — not accepted |
| 25337 | R1Z/PV_Src_AdmissionOccupiedScan | 0 | 0:01.96 | 4108184 | 0 | 597a70c88c | standard only |
| 25338 | R1Z/PV_Src_ExternalLanes | 0 | 0:01.97 | 4103968 | 0 | 597a70c88c | standard only |
| 25341 | R1Z/PV_Src_ExternalTotal | 1 | 0:01.65 | 4080696 | 0 | 597a70c88c | FAILED — not accepted |
| 25342 | R1Z/PV_Src_ExternalTotal | 0 | 0:01.90 | 4099040 | 0 | 597a70c88c | standard only |
| 25343 | R1Z/PV_Src_AdmissionOccupied | 1 | 0:02.17 | 4088860 | 0 | 597a70c88c | FAILED — not accepted |
| 25344 | R1Z/PV_Src_AdmissionOccupied | 1 | 0:01.76 | 4089756 | 0 | 597a70c88c | FAILED — not accepted |
| 25345 | R1Z/PV_Src_AdmissionOccupied | 1 | 0:01.85 | 4089972 | 0 | 597a70c88c | FAILED — not accepted |
| 25346 | R1Z/PV_Src_AdmissionOccupied | 1 | 0:02.46 | 4092220 | 0 | 597a70c88c | FAILED — not accepted |
| 25347 | R1Z/PV_Src_AdmissionOccupied | 1 | 0:02.50 | 4091352 | 0 | 597a70c88c | FAILED — not accepted |
| 25348 | R1Z/PV_Src_AdmissionOccupied | 0 | 0:02.69 | 4112292 | 0 | 597a70c88c | standard only |
| 25350 | R1Z/PV_Src_AdmissionCommonSuccess | 1 | 0:01.86 | 4090136 | 0 | ffe728a965 | FAILED — not accepted |
| 25351 | R1Z/PV_Src_AdmissionCommonSuccess | 1 | 0:02.02 | 4088740 | 0 | ffe728a965 | FAILED — not accepted |
| 25352 | R1Z/PV_Src_AdmissionCommonSuccess | 1 | 0:01.96 | 4089952 | 0 | ffe728a965 | FAILED — not accepted |
| 25355 | R1Z/PV_Src_AdmissionCommonSuccess | 0 | 0:01.98 | 4112060 | 0 | b58a2abed8 | standard only |
| 25356 | R1Z/PV_Src_FixturePairValidation | 1 | 0:01.79 | 4203832 | 0 | b58a2abed8 | FAILED — not accepted |
| 25357 | R1Z/PV_Src_FixturePairValidation | 0 | 0:01.92 | 4224928 | 0 | b58a2abed8 | standard only |
| 25358 | R1Z/PV_Src_FixtureCommonValidation | 0 | 0:01.98 | 4219864 | 0 | b58a2abed8 | standard only |
| 25359 | R1Z/PV_Src_FixtureCheckedSource | 1 | 0:23.09 | 4198196 | 0 | b58a2abed8 | FAILED — not accepted |
| 25360 | R1Z/PV_Src_FixtureValidationInputs | 0 | 0:01.90 | 4218860 | 0 | b58a2abed8 | standard only |
| 25361 | R1Z/PV_Src_FixtureCheckedSource | 0 | 0:02.03 | 4220840 | 0 | b58a2abed8 | standard only |
| 25362 | R1Z/PV_Src_CanonicalSnapshot | 0 | 0:01.96 | 4105448 | 0 | 6bd084087c | standard only |
| 25364 | R1Z/PV_Src_CanonicalRoots | 1 | 0:01.91 | 4094732 | 0 | 6bd084087c | FAILED — not accepted |
| 25365 | R1Z/PV_Src_CanonicalRoots | 0 | 0:01.95 | 4116944 | 0 | 6bd084087c | standard only |
| 25366 | R1Z/PV_Src_FrozenInput | 0 | 0:01.86 | 4120256 | 0 | 6bd084087c | standard only |
| 25368 | R1Z/PV_Src_FrozenPublic | 0 | 0:01.79 | 4110688 | 0 | 6bd084087c | standard only |
| 25369 | R1Z/PV_Src_SelectedThree | 0 | 0:01.84 | 4118308 | 0 | 6bd084087c | standard only |
| 25370 | R1Z/PV_Src_ThreeConsumer | 0 | 0:02.37 | 4240088 | 0 | 6bd084087c | standard only |
| 25371 | R1Z/PV_Src_FrozenStages | 0 | 0:01.81 | 4224876 | 0 | 6bd084087c | standard only |
| 25372 | R1Z/PV_Src_PathPacking | 0 | 0:02.08 | 4099516 | 0 | e741b18d00 | standard only |
| 25373 | R1Z/PV_Src_PathIndex | 1 | 0:01.97 | 4096816 | 0 | e741b18d00 | FAILED — not accepted |
| 25374 | R1Z/PV_Src_PathIndex | 0 | 0:02.17 | 4118132 | 0 | e741b18d00 | standard only |
| 25375 | R1Z/PV_Src_PathBits | 1 | 0:01.93 | 4083288 | 0 | e741b18d00 | FAILED — not accepted |
| 25376 | R1Z/PV_Src_PathBits | 1 | 0:01.86 | 4087500 | 0 | e741b18d00 | FAILED — not accepted |
| 25377 | R1Z/PV_Src_PathBits | 1 | 0:01.81 | 4087144 | 0 | e741b18d00 | FAILED — not accepted |
| 25378 | R1Z/PV_Src_PathBits | 0 | 0:02.02 | 4106168 | 0 | e741b18d00 | standard only |
| 25380 | R1Z/PV_Src_CanonicalSibling | 0 | 0:01.82 | 4107336 | 0 | 6b8c433166 | standard only |
| 25381 | R1Z/PV_Src_PathSiblings | 1 | 0:01.92 | 4086140 | 0 | 6b8c433166 | FAILED — not accepted |
| 25382 | R1Z/PV_Src_PathSiblings | 0 | 0:01.86 | 4106740 | 0 | 6b8c433166 | standard only |
| 25383 | R1Z/PV_Src_ReferenceTransfer | 0 | 0:01.73 | 4107388 | 0 | 6b8c433166 | standard only |
| 25384 | R1Z/PV_Src_ReduceModulo | 0 | 0:01.75 | 4109972 | 0 | 6b8c433166 | standard only |
| 25385 | R1Z/PV_Src_ExternalMat4Copy | 1 | 0:01.72 | 4087724 | 0 | 6b8c433166 | FAILED — not accepted |
| 25386 | R1Z/PV_Src_ExternalMat4Copy | 0 | 0:01.79 | 4106972 | 0 | 6b8c433166 | standard only |
| 25387 | R1Z/PV_Src_FrozenFixtures | 0 | 0:02.36 | 4229644 | 0 | 6b8c433166 | standard only |
| 25388 | R1Z/PV_Src_ExternalCanonical | 0 | 0:02.09 | 4107760 | 0 | 6b8c433166 | standard only |
| 25389 | R1Z/PV_Src_WithdrawalRecipient | 0 | 0:02.82 | 4080172 | 0 | cef0887322 | standard only |
| 25390 | R1Z/PV_Src_ReferenceWithdrawal | 1 | 0:02.91 | 4075540 | 0 | cef0887322 | FAILED — not accepted |
| 25391 | R1Z/PV_Src_ReferenceWithdrawal | 1 | 0:03.36 | 4069752 | 0 | cef0887322 | FAILED — not accepted |
| 25392 | R1Z/PV_Src_ZeroDigest | 1 | 0:03.20 | 4065776 | 0 | cef0887322 | FAILED — not accepted |
| 25393 | R1Z/PV_Src_ZeroDigest | 1 | 0:03.83 | 4068532 | 0 | cef0887322 | FAILED — not accepted |
| 25394 | R1Z/PV_Src_ZeroDigest | 1 | 0:02.63 | 4068424 | 0 | cef0887322 | FAILED — not accepted |
| 25395 | R1Z/PV_Src_ZeroDigest | 0 | 0:02.58 | 4089624 | 0 | cef0887322 | standard only |
| 25396 | R1Z/PV_Src_ReferenceWithdrawal | 0 | 0:02.07 | 4105744 | 0 | cef0887322 | standard only |
| 25397 | R1Z/PV_Src_CanonicalDecode | 1 | 0:01.93 | 4066860 | 0 | cef0887322 | FAILED — not accepted |
| 25398 | R1Z/PV_Src_CanonicalDecode | 0 | 0:02.51 | 4080944 | 0 | cef0887322 | standard only |
| 25399 | R1Z/PV_Src_RecordAdmission | 1 | 0:02.25 | 4062876 | 0 | cef0887322 | FAILED — not accepted |
| 25400 | R1Z/PV_Src_RecordAdmission | 0 | 0:02.22 | 4097864 | 0 | cef0887322 | standard only |

## Kani

All commands optimized via explicit MIR/Rust flags, 6G/8G/swap0/tasks64; exact commands and source hashes in each receipt.
#print axioms: N/A for Rust/Kani. Cgroup peak is aggregate; timed-out parent `/usr/bin/time` RSS may omit killed descendants.

| # | Target | Exit | Wall sec | RSS KiB | Aggregate peak bytes | Swap | Revision | Checks failed/total |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 1 | srcid3-metadata | 0 | 13.637 | 1234252 | 1415397376 | 0 | 597a70c88c | no verification result |
| 2 | pool_v1::pair_forest_copy_builder::records_proofs::pv_srcid3::pv_srcid3_full_mapper | 124 | 480.008 | 15824 | 3857346560 | 0 | 597a70c88c | no verification result |
| 3 | poseidon2::builder_reference::pv_srcid3_external_owned_unstubbed | 0 | 154.122 | 703936 | 758218752 | 0 | 597a70c88c | 0/571 |
| 4 | metadata | 0 | 8.379 | 1384684 | 1430081536 | 0 | e741b18d00 | no verification result |
| 5 | pool_v1::pair_forest_copy_builder::records_proofs::pv_srcid3::pv_srcid3_mapper_values | 124 | 180.008 | 15652 | 2679185408 | 0 | e741b18d00 | no verification result |
| 6 | pool_v1::pair_forest_copy_builder::records_proofs::pv_srcid3::pv_srcid3_mapper_path | 124 | 180.003 | 14960 | 2815766528 | 0 | 2ef4f10506 | no verification result |
| 7 | pool_v1::pair_forest_copy_builder::records_proofs::pv_srcid3::pv_srcid3_mapper_digests | 124 | 180.003 | 15136 | 2805563392 | 0 | 2ef4f10506 | no verification result |
| 8 | pool_v1::pair_forest_copy_builder::records_proofs::pv_srcid3::pv_srcid3_mapper_public | 124 | 180.008 | 15300 | 2727071744 | 0 | 8daf67c70f | no verification result |
| 9 | pool_v1::pair_forest_copy_builder::records_proofs::pv_srcid3::pv_srcid3_common_values | 0 | 23.505 | 892652 | 1029947392 | 0 | 8daf67c70f | 0/448 |
| 10 | pool_v1::pair_forest_copy_builder::records_proofs::pv_srcid3::pv_srcid3_common_sibling | 0 | 21.655 | 909784 | 1036906496 | 0 | 8daf67c70f | 0/451 |
| 11 | pool_v1::pair_forest_copy_builder::records_proofs::pv_srcid3::pv_srcid3_common_pair_words | 0 | 21.897 | 888856 | 1018671104 | 0 | 8daf67c70f | 0/452 |
| 12 | pool_v1::pair_forest_copy_builder::records_proofs::empty_roots::pv_srcid3_empty_roots_full | 124 | 180.008 | 15300 | 2510073856 | 0 | 8daf67c70f | no verification result |
