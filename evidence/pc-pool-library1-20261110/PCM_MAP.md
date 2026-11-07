# PCM Pool slot map

Supporting work only; no row credit. All unfilled slots have exactly one prescribed classification. A supplier packet marked CLOSED below is still subject to PCM combined-import/revalidation; no unvalidated packet is promoted.

| Slot | Supplier | Classification | Needed bridge / caller |
|---|---|---|---|
| POOL:294.Children.encode | POOL:187  | OPEN-ROW | POOL:294 at this SAME source call; representation by its native cut/entry admission |
| POOL:294.Children.canonicalNullifier | POOL:184 PCG_MarkerCodec.row_184 | MISSING-CHILD-LEMMA | PCM_adapter_294_canonicalNullifier |
| POOL:294.Children.address | POOL:297  | OPEN-ROW | POOL:294 at this SAME source call; representation by its native cut/entry admission |
| POOL:294.Children.classify | POOL:292  | OPEN-ROW | POOL:294 at this SAME source call; representation by its native cut/entry admission |
| POOL:319.Children.nextLane | POOL:320 PCD_Row320.result_state_effects | MISSING-CHILD-LEMMA | PCM_adapter_319_nextLane |
| POOL:319.Children.encodeLane | POOL:315  | OPEN-ROW | POOL:319 at this SAME source call; representation by its native cut/entry admission |
| POOL:321.Children.aliasFree | POOL:331  | OPEN-ROW | POOL:321 at this SAME source call; representation by its native cut/entry admission |
| POOL:321.Children.master | POOL:303  | OPEN-ROW | POOL:321 at this SAME source call; representation by its native cut/entry admission |
| POOL:321.Children.lanes | POOL:302  | OPEN-ROW | POOL:321 at this SAME source call; representation by its native cut/entry admission |
| POOL:321.Children.globalRoot | POOL:324 PCG_GlobalLaw.row_324 | MISSING-CHILD-LEMMA | PCM_adapter_321_globalRoot |
| POOL:321.Children.checkpointAddress | POOL:323 PCG_CheckpointAddress.row_323 | MISSING-CHILD-LEMMA | PCM_adapter_321_checkpointAddress |
| POOL:321.Children.purePlan | POOL:198  | OPEN-ROW | POOL:321 at this SAME source call; representation by its native cut/entry admission |
| POOL:321.Children.freshPda | POOL:362  | OPEN-ROW | POOL:321 at this SAME source call; representation by its native cut/entry admission |
| POOL:321.Children.encodeMaster | POOL:196  | OPEN-ROW | POOL:321 at this SAME source call; representation by its native cut/entry admission |
| POOL:321.Children.encodeCheckpoint | POOL:194  | OPEN-ROW | POOL:321 at this SAME source call; representation by its native cut/entry admission |
| POOL:322.Children.zeroedPage | POOL:301  | OPEN-ROW | POOL:322 at this SAME source call; representation by its native cut/entry admission |
| POOL:322.Children.address | POOL:284  | OPEN-ROW | POOL:322 at this SAME source call; representation by its native cut/entry admission |
| POOL:322.Children.programAccount | POOL:282  | OPEN-ROW | POOL:322 at this SAME source call; representation by its native cut/entry admission |
| POOL:322.Children.currentPage | POOL:340  | OPEN-ROW | POOL:322 at this SAME source call; representation by its native cut/entry admission |
| POOL:322.Children.exactCount | POOL:332 PCI_CountState.complete | MISSING-CHILD-LEMMA | PCM_adapter_322_exactCount |
| POOL:322.Children.uniqueAccounts | POOL:367  | OPEN-ROW | POOL:322 at this SAME source call; representation by its native cut/entry admission |
| POOL:326.Children.append | POOL:181 PCG_OwnedTree.row_181 | MISSING-CHILD-LEMMA | PCM_adapter_326_append |
| POOL:326.Children.encode | POOL:195  | OPEN-ROW | POOL:326 at this SAME source call; representation by its native cut/entry admission |
| POOL:327.Children.exactCount | POOL:332 PCI_CountState.complete | MISSING-CHILD-LEMMA | PCM_adapter_327_exactCount |
| POOL:327.Children.uniqueAccounts | POOL:367  | OPEN-ROW | POOL:327 at this SAME source call; representation by its native cut/entry admission |
| POOL:327.Children.payerAndSystem | POOL:364 PCF_Payer.result_state_effects | MISSING-CHILD-LEMMA | PCM_adapter_327_payerAndSystem |
| POOL:327.Children.planCheckpoint | POOL:321  | OPEN-ROW | POOL:327 at this SAME source call; representation by its native cut/entry admission |
| POOL:327.Children.freshPda | POOL:362  | OPEN-ROW | POOL:327 at this SAME source call; representation by its native cut/entry admission |
| POOL:327.Children.decodeCheckpoint | POOL:190 ['NJY_Roots.checkpoint', 'NJQ_Checkpoint.source', 'NJQ_Canonical.checkpoint_result'] | MISSING-CHILD-LEMMA | PCM_adapter_327_decodeCheckpoint |
| POOL:327.Children.createPda | POOL:358  | OPEN-ROW | POOL:327 at this SAME source call; representation by its native cut/entry admission |
| POOL:327.Children.programOwnedZeroed | POOL:333  | OPEN-ROW | POOL:327 at this SAME source call; representation by its native cut/entry admission |
| POOL:328.Children.decodeMaster | POOL:313  | OPEN-ROW | POOL:328 at this SAME source call; representation by its native cut/entry admission |
| POOL:328.Children.noteCommitment | POOL:165  | OPEN-ROW | POOL:328 at this SAME source call; representation by its native cut/entry admission |
| POOL:328.Children.depositLane | POOL:199 PCF_LaneModel.complete | MISSING-CHILD-LEMMA | PCM_adapter_328_depositLane |
| POOL:328.Children.decodeLane | POOL:304  | OPEN-ROW | POOL:328 at this SAME source call; representation by its native cut/entry admission |
| POOL:328.Children.singleOutput | POOL:222 PCI_SinglePacket.full | MISSING-CHILD-LEMMA | PCM_adapter_328_singleOutput |
| POOL:328.Children.leafDigest | POOL:220  | OPEN-ROW | POOL:328 at this SAME source call; representation by its native cut/entry admission |
| POOL:328.Children.prepareAppend | POOL:326  | OPEN-ROW | POOL:328 at this SAME source call; representation by its native cut/entry admission |
| POOL:328.Children.rootLocation | POOL:246 PCB_Location.result | MISSING-CHILD-LEMMA | PCM_adapter_328_rootLocation |
| POOL:328.Children.zeroedPage | POOL:301  | OPEN-ROW | POOL:328 at this SAME source call; representation by its native cut/entry admission |
| POOL:328.Children.pageAddress | POOL:280 PCI_RootAddress.complete | MISSING-CHILD-LEMMA | PCM_adapter_328_pageAddress |
| POOL:328.Children.freshPda | POOL:362  | OPEN-ROW | POOL:328 at this SAME source call; representation by its native cut/entry admission |
| POOL:328.Children.currentPage | POOL:340  | OPEN-ROW | POOL:328 at this SAME source call; representation by its native cut/entry admission |
| POOL:328.Children.exactCount | POOL:332 PCI_CountState.complete | MISSING-CHILD-LEMMA | PCM_adapter_328_exactCount |
| POOL:328.Children.uniqueAccounts | POOL:367  | OPEN-ROW | POOL:328 at this SAME source call; representation by its native cut/entry admission |
| POOL:328.Children.tokenProgram | POOL:365 PCF_Token.result_state_effects | MISSING-CHILD-LEMMA | PCM_adapter_328_tokenProgram |
| POOL:328.Children.planTransfer | POOL:388  | OPEN-ROW | POOL:328 at this SAME source call; representation by its native cut/entry admission |
| POOL:328.Children.transferInfos | POOL:382  | OPEN-ROW | POOL:328 at this SAME source call; representation by its native cut/entry admission |
| POOL:328.Children.payerAndSystem | POOL:364 PCF_Payer.result_state_effects | MISSING-CHILD-LEMMA | PCM_adapter_328_payerAndSystem |
| POOL:328.Children.createPda | POOL:358  | OPEN-ROW | POOL:328 at this SAME source call; representation by its native cut/entry admission |
| POOL:328.Children.programOwnedZeroed | POOL:333  | OPEN-ROW | POOL:328 at this SAME source call; representation by its native cut/entry admission |
| POOL:328.Children.exactDelta | POOL:395  | OPEN-ROW | POOL:328 at this SAME source call; representation by its native cut/entry admission |
| POOL:328.Children.writeNewPage | POOL:286  | OPEN-ROW | POOL:328 at this SAME source call; representation by its native cut/entry admission |
| POOL:328.Children.appendRoots | POOL:279  | OPEN-ROW | POOL:328 at this SAME source call; representation by its native cut/entry admission |
| POOL:330.Children.decodeRequest | POOL:314 PCD_RequestRoot.result_state_effects | MISSING-CHILD-LEMMA | PCM_adapter_330_decodeRequest |
| POOL:330.Children.decodeMaster | POOL:313  | OPEN-ROW | POOL:330 at this SAME source call; representation by its native cut/entry admission |
| POOL:330.Children.decodeCheckpoint | POOL:311  | OPEN-ROW | POOL:330 at this SAME source call; representation by its native cut/entry admission |
| POOL:330.Children.outputLane | POOL:200 ['NFY_NEM_LaneReached.lane_instance', 'NFY_NEM_LaneReached.lane_reached', 'NFY_NEM_LaneReached.lane_instance', 'NFY_NEM_LaneReached.lane_reached'] | MISSING-CHILD-LEMMA | PCM_adapter_330_outputLane |
| POOL:330.Children.decodeLane | POOL:312  | OPEN-ROW | POOL:330 at this SAME source call; representation by its native cut/entry admission |
| POOL:330.Children.requestAccounts | POOL:341  | OPEN-ROW | POOL:330 at this SAME source call; representation by its native cut/entry admission |
| POOL:330.Children.spendLayout | POOL:322  | OPEN-ROW | POOL:330 at this SAME source call; representation by its native cut/entry admission |
| POOL:330.Children.payerAndSystem | POOL:364 PCF_Payer.result_state_effects | MISSING-CHILD-LEMMA | PCM_adapter_330_payerAndSystem |
| POOL:330.Children.planMarker | POOL:294  | OPEN-ROW | POOL:330 at this SAME source call; representation by its native cut/entry admission |
| POOL:330.Children.tokenProgram | POOL:365 PCF_Token.result_state_effects | MISSING-CHILD-LEMMA | PCM_adapter_330_tokenProgram |
| POOL:330.Children.planWithdrawal | POOL:389  | OPEN-ROW | POOL:330 at this SAME source call; representation by its native cut/entry admission |
| POOL:330.Children.createMarker | POOL:361  | OPEN-ROW | POOL:330 at this SAME source call; representation by its native cut/entry admission |
| POOL:330.Children.verify | POOL:347  | OPEN-ROW | POOL:330 at this SAME source call; representation by its native cut/entry admission |
| POOL:330.Children.validateResult | POOL:339  | OPEN-ROW | POOL:330 at this SAME source call; representation by its native cut/entry admission |
| POOL:330.Children.nextLaneImage | POOL:319  | OPEN-ROW | POOL:330 at this SAME source call; representation by its native cut/entry admission |
| POOL:330.Children.resultBytes | POOL:337  | OPEN-ROW | POOL:330 at this SAME source call; representation by its native cut/entry admission |
| POOL:330.Children.withdrawalInfos | POOL:383  | OPEN-ROW | POOL:330 at this SAME source call; representation by its native cut/entry admission |
| POOL:330.Children.exactDelta | POOL:396  | OPEN-ROW | POOL:330 at this SAME source call; representation by its native cut/entry admission |
| POOL:330.Children.writeNewPage | POOL:286  | OPEN-ROW | POOL:330 at this SAME source call; representation by its native cut/entry admission |
| POOL:330.Children.appendRoots | POOL:279  | OPEN-ROW | POOL:330 at this SAME source call; representation by its native cut/entry admission |
| POOL:330.Children.setReturnData | POOL:330  | OPEN-ROW | POOL:330 at this SAME source call; representation by its native cut/entry admission |
| POOL:333.Children.programAccount | POOL:282  | OPEN-ROW | POOL:333 at this SAME source call; representation by its native cut/entry admission |
| POOL:333.Children.rentExempt | POOL:333  | OPEN-ROW | POOL:333 at this SAME source call; representation by its native cut/entry admission |
| POOL:339.Children.validate | POOL:213 ['NFY_NEY_BindingContinuation.result', 'NFY_NEY_BindingSuccess.binding_success', 'NGF_NEY_ReachedResultDomains.binding_argument'] | MISSING-CHILD-LEMMA | PCM_adapter_339_validate |
| POOL:340.Children.programAccount | POOL:282  | OPEN-ROW | POOL:340 at this SAME source call; representation by its native cut/entry admission |
| POOL:340.Children.addressWithBump | POOL:284  | OPEN-ROW | POOL:340 at this SAME source call; representation by its native cut/entry admission |
| POOL:340.Children.address | POOL:283  | OPEN-ROW | POOL:340 at this SAME source call; representation by its native cut/entry admission |
| POOL:340.Children.validatePage | POOL:285  | OPEN-ROW | POOL:340 at this SAME source call; representation by its native cut/entry admission |
| POOL:340.Children.retainedRoot | POOL:281  | OPEN-ROW | POOL:340 at this SAME source call; representation by its native cut/entry admission |
| POOL:341.Children.outputLane | POOL:200 ['NFY_NEM_LaneReached.lane_instance', 'NFY_NEM_LaneReached.lane_reached', 'NFY_NEM_LaneReached.lane_instance', 'NFY_NEM_LaneReached.lane_reached'] | MISSING-CHILD-LEMMA | PCM_adapter_341_outputLane |
| POOL:341.Children.laneMatches | POOL:317  | OPEN-ROW | POOL:341 at this SAME source call; representation by its native cut/entry admission |
| POOL:347.Children.plan | POOL:349  | OPEN-ROW | POOL:347 at this SAME source call; representation by its native cut/entry admission |
| POOL:347.Children.invoke | POOL:348  | OPEN-ROW | POOL:347 at this SAME source call; representation by its native cut/entry admission |
| POOL:348.Children.requireProgram | POOL:353  | OPEN-ROW | POOL:348 at this SAME source call; representation by its native cut/entry admission |
| POOL:348.Children.proofTransport | POOL:351  | OPEN-ROW | POOL:348 at this SAME source call; representation by its native cut/entry admission |
| POOL:348.Children.distinctCheckpoint | POOL:352  | OPEN-ROW | POOL:348 at this SAME source call; representation by its native cut/entry admission |
| POOL:348.Children.decodeResult | POOL:208  | OPEN-ROW | POOL:348 at this SAME source call; representation by its native cut/entry admission |
| POOL:349.Children.encode | POOL:209  | OPEN-ROW | POOL:349 at this SAME source call; representation by its native cut/entry admission |
| POOL:349.Children.plan | POOL:350  | OPEN-ROW | POOL:349 at this SAME source call; representation by its native cut/entry admission |
| POOL:350.Children.proofTransport | POOL:351  | OPEN-ROW | POOL:350 at this SAME source call; representation by its native cut/entry admission |
| POOL:350.Children.requireProgram | POOL:353  | OPEN-ROW | POOL:350 at this SAME source call; representation by its native cut/entry admission |
| POOL:350.Children.distinctCheckpoint | POOL:352  | OPEN-ROW | POOL:350 at this SAME source call; representation by its native cut/entry admission |
| POOL:350.Children.authenticate | POOL:372  | OPEN-ROW | POOL:350 at this SAME source call; representation by its native cut/entry admission |
| POOL:350.Children.matchesOwner | POOL:371 PCB_RegistryLaws.owner | MISSING-CHILD-LEMMA | PCM_adapter_350_matchesOwner |
| POOL:350.Children.matchesSelection | POOL:370 PCB_RegistryLaws.selection | MISSING-CHILD-LEMMA | PCM_adapter_350_matchesSelection |
| POOL:358.Children.rentGet | POOL:358  | OPEN-ROW | POOL:358 at this SAME source call; representation by its native cut/entry admission |
| POOL:358.Children.withRent | POOL:359  | OPEN-ROW | POOL:358 at this SAME source call; representation by its native cut/entry admission |
| POOL:361.Children.seedString | POOL:296 PCG_MarkerSeed.row_296 | MISSING-CHILD-LEMMA | PCM_adapter_361_seedString |
| POOL:361.Children.createWithSeed | POOL:360  | OPEN-ROW | POOL:361 at this SAME source call; representation by its native cut/entry admission |
| POOL:361.Children.recheck | POOL:298  | OPEN-ROW | POOL:361 at this SAME source call; representation by its native cut/entry admission |
| POOL:361.Children.rentExempt | POOL:361  | OPEN-ROW | POOL:361 at this SAME source call; representation by its native cut/entry admission |
| POOL:388.Children.ownedAccount | POOL:392  | OPEN-ROW | POOL:388 at this SAME source call; representation by its native cut/entry admission |
| POOL:388.Children.mint | POOL:386  | OPEN-ROW | POOL:388 at this SAME source call; representation by its native cut/entry admission |
| POOL:388.Children.token | POOL:387  | OPEN-ROW | POOL:388 at this SAME source call; representation by its native cut/entry admission |
| POOL:388.Children.vaultAddress | POOL:391 PCG_AddressRoots.row_391 | MISSING-CHILD-LEMMA | PCM_adapter_388_vaultAddress |
| POOL:388.Children.authorityAddress | POOL:390 PCG_AddressRoots.row_390 | MISSING-CHILD-LEMMA | PCM_adapter_388_authorityAddress |
| POOL:388.Children.storedBumpMatches | POOL:379 PCG_AddressRoots.row_379 | MISSING-CHILD-LEMMA | PCM_adapter_388_storedBumpMatches |
| POOL:389.Children.ownedAccount | POOL:392  | OPEN-ROW | POOL:389 at this SAME source call; representation by its native cut/entry admission |
| POOL:389.Children.mint | POOL:386  | OPEN-ROW | POOL:389 at this SAME source call; representation by its native cut/entry admission |
| POOL:389.Children.token | POOL:387  | OPEN-ROW | POOL:389 at this SAME source call; representation by its native cut/entry admission |
| POOL:389.Children.vaultAddress | POOL:391 PCG_AddressRoots.row_391 | MISSING-CHILD-LEMMA | PCM_adapter_389_vaultAddress |
| POOL:389.Children.authorityAddress | POOL:390 PCG_AddressRoots.row_390 | MISSING-CHILD-LEMMA | PCM_adapter_389_authorityAddress |
| POOL:389.Children.storedBumpMatches | POOL:379 PCG_AddressRoots.row_379 | MISSING-CHILD-LEMMA | PCM_adapter_389_storedBumpMatches |
| POOL:395.Children.ownedAccount | POOL:392  | OPEN-ROW | POOL:395 at this SAME source call; representation by its native cut/entry admission |
| POOL:395.Children.mint | POOL:386  | OPEN-ROW | POOL:395 at this SAME source call; representation by its native cut/entry admission |
| POOL:395.Children.token | POOL:387  | OPEN-ROW | POOL:395 at this SAME source call; representation by its native cut/entry admission |
| POOL:395.Children.vaultAddress | POOL:391 PCG_AddressRoots.row_391 | MISSING-CHILD-LEMMA | PCM_adapter_395_vaultAddress |
| POOL:395.Children.authorityAddress | POOL:390 PCG_AddressRoots.row_390 | MISSING-CHILD-LEMMA | PCM_adapter_395_authorityAddress |
| POOL:395.Children.storedBumpMatches | POOL:379 PCG_AddressRoots.row_379 | MISSING-CHILD-LEMMA | PCM_adapter_395_storedBumpMatches |
| POOL:396.Children.ownedAccount | POOL:392  | OPEN-ROW | POOL:396 at this SAME source call; representation by its native cut/entry admission |
| POOL:396.Children.mint | POOL:386  | OPEN-ROW | POOL:396 at this SAME source call; representation by its native cut/entry admission |
| POOL:396.Children.token | POOL:387  | OPEN-ROW | POOL:396 at this SAME source call; representation by its native cut/entry admission |
| POOL:396.Children.vaultAddress | POOL:391 PCG_AddressRoots.row_391 | MISSING-CHILD-LEMMA | PCM_adapter_396_vaultAddress |
| POOL:396.Children.authorityAddress | POOL:390 PCG_AddressRoots.row_390 | MISSING-CHILD-LEMMA | PCM_adapter_396_authorityAddress |
| POOL:396.Children.storedBumpMatches | POOL:379 PCG_AddressRoots.row_379 | MISSING-CHILD-LEMMA | PCM_adapter_396_storedBumpMatches |
| POOL:311.Decoder/SDK | POOL:310  | OPEN-ROW | POOL:311; same input and writable flag (312 true, 313 false, 304 generic decoder true) |
| POOL:312.Decoder/SDK | POOL:306  | OPEN-ROW | POOL:312; same input and writable flag (312 true, 313 false, 304 generic decoder true) |
| POOL:313.Decoder/SDK | POOL:307  | OPEN-ROW | POOL:313; same input and writable flag (312 true, 313 false, 304 generic decoder true) |
| POOL:314.Decoder/SDK | POOL:207 ['NFY_NFD_RequestDomains.binding_fields', 'NFY_NFD_RequestDomains.payment_length', 'NFY_NFD_RequestDomains.payment_window', 'NFY_NFD_RequestDomains.wrong_length', 'NFY_NFD_RequestField00.alignment', 'NFY_NFD_RequestField01.alignment', 'NFY_NFD_RequestField02.alignment', 'NFY_NFD_RequestField03.alignment', 'NFY_NFD_RequestField04.alignment', 'NFY_NFD_RequestField05.alignment', 'NFY_NFD_RequestField06.alignment', 'NFY_NFD_RequestField07.alignment', 'NFY_NFD_RequestField08.alignment', 'NFY_NFD_RequestField09.alignment', 'NFY_NFD_RequestField10.alignment', 'NFY_NFD_RequestField11.alignment', 'NFY_NFD_RequestField12.alignment', 'NFY_NFD_RequestField13.alignment', 'NFY_NFD_RequestOracle.array_result_state_effects', 'NFY_NFD_RequestOracle.result_state_effects', 'NFY_NFD_RequestProjection.complete', 'NFY_NFD_RequestProjection.transfer_roundtrip', 'NFY_NFD_RequestProjection.withdrawal_roundtrip'] | MISSING-CHILD-LEMMA | PCM_adapter_314_decoder |
| POOL:304.Decoder/SDK | POOL:305  | OPEN-ROW | POOL:304; same input and writable flag (312 true, 313 false, 304 generic decoder true) |
| POOL:337.Decoder/SDK | POOL:209  | OPEN-ROW | POOL:337; same input and writable flag (312 true, 313 false, 304 generic decoder true) |
| POOL:356.Decoder/SDK | POOL:356  | OPEN-ROW | POOL:356; same input and writable flag (312 true, 313 false, 304 generic decoder true) |
| POOL:357.Decoder/SDK | POOL:357  | OPEN-ROW | POOL:357; same input and writable flag (312 true, 313 false, 304 generic decoder true) |
| RSL.PoolLib.Request | [] | MISSING-CHILD-LEMMA | PCM_shared_Request |
| RSL.PoolLib.Statement | [] | MISSING-CHILD-LEMMA | PCM_shared_Statement |
| RSL.PoolLib.Afterstate | [] | MISSING-CHILD-LEMMA | PCM_shared_Afterstate |
| RSL.PoolLib.decodeRequest | [{'row': 'TX2:163', 'status': 'CLOSED', 'function': 'crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::decode_pool_v1_pair_forest_terminal_request_v1', 'owner_module': 'NFY_Part059', 'roots': ['NFY_NFD_RequestDomains.binding_fields', 'NFY_NFD_RequestDomains.payment_length', 'NFY_NFD_RequestDomains.payment_window', 'NFY_NFD_RequestDomains.wrong_length', 'NFY_NFD_RequestField00.alignment', 'NFY_NFD_RequestField01.alignment', 'NFY_NFD_RequestField02.alignment', 'NFY_NFD_RequestField03.alignment', 'NFY_NFD_RequestField04.alignment', 'NFY_NFD_RequestField05.alignment', 'NFY_NFD_RequestField06.alignment', 'NFY_NFD_RequestField07.alignment', 'NFY_NFD_RequestField08.alignment', 'NFY_NFD_RequestField09.alignment', 'NFY_NFD_RequestField10.alignment', 'NFY_NFD_RequestField11.alignment', 'NFY_NFD_RequestField12.alignment', 'NFY_NFD_RequestField13.alignment', 'NFY_NFD_RequestOracle.array_result_state_effects', 'NFY_NFD_RequestOracle.result_state_effects', 'NFY_NFD_RequestProjection.complete', 'NFY_NFD_RequestProjection.transfer_roundtrip', 'NFY_NFD_RequestProjection.withdrawal_roundtrip']}] | MISSING-CHILD-LEMMA | PCM_shared_decodeRequest |
| RSL.PoolLib.reqProfile | [] | MISSING-CHILD-LEMMA | PCM_shared_reqProfile |
| RSL.PoolLib.reqRelease | [] | MISSING-CHILD-LEMMA | PCM_shared_reqRelease |
| RSL.PoolLib.reqPoolProgram | [] | MISSING-CHILD-LEMMA | PCM_shared_reqPoolProgram |
| RSL.PoolLib.reqNullifier | [{'row': 'TX2:158', 'status': 'CLOSED', 'function': 'crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalPaymentV1::nullifier', 'owner_module': 'NGE_NEQ_NullifierDomains', 'roots': ['NGE_NEQ_NullifierDomains.common_independent', 'NGE_NEQ_NullifierDomains.payment_result_frame', 'NGE_NEQ_NullifierDomains.statement_result_frame']}] | MISSING-CHILD-LEMMA | PCM_shared_reqNullifier |
| RSL.PoolLib.outputLane | [{'row': 'TX2:156', 'status': 'CLOSED', 'function': 'crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::pool_v1_pair_forest_output_lane_v1', 'owner_module': 'NFY_Part031', 'roots': ['NFY_NEM_LaneReached.lane_instance', 'NFY_NEM_LaneReached.lane_reached']}] | MISSING-CHILD-LEMMA | PCM_shared_outputLane |
| RSL.PoolLib.decodeMaster | [{'row': 'TX2:153', 'status': 'CLOSED', 'function': 'crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::decode_pool_v1_pair_forest_master_v1', 'owner_module': 'NJY_Roots', 'roots': ['NJY_Roots.master', 'NJQ_Master.source', 'NJQ_Canonical.master_result']}] | MISSING-CHILD-LEMMA | PCM_shared_decodeMaster |
| RSL.PoolLib.decodeCheckpoint | [{'row': 'TX2:152', 'status': 'CLOSED', 'function': 'crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::decode_pool_v1_pair_forest_checkpoint_v1', 'owner_module': 'NJY_Roots', 'roots': ['NJY_Roots.checkpoint', 'NJQ_Checkpoint.source', 'NJQ_Canonical.checkpoint_result']}] | MISSING-CHILD-LEMMA | PCM_shared_decodeCheckpoint |
| RSL.PoolLib.validatePolicy | [{'row': 'TX2:151', 'status': 'CLOSED', 'function': 'crates/aspis-statement/src/pool_v1/format.rs::validate_verifier_policy_v1', 'owner_module': 'NHY_PolicyModel', 'roots': ['NHY_PolicyModel.actual_slot']}] | MISSING-CHILD-LEMMA | Pool owner at the same argument; RuntimeEntrypointAdmission-Pool for cell identity; EnvRep for the one headline reservation |
| RSL.PoolLib.decodeRegistryV1 | [{'row': 'TX2:203', 'status': 'CLOSED', 'function': 'crates/aspis-statement/src/pool_v1/verifier_registry.rs::decode_verifier_registry_v1', 'owner_module': 'NJY_Roots', 'roots': ['NJY_Roots.registry', 'NJQ_Registry.source', 'NJQ_Canonical.registry_result']}] | MISSING-CHILD-LEMMA | Pool owner at the same argument; RuntimeEntrypointAdmission-Pool for cell identity; EnvRep for the one headline reservation |
| RSL.PoolLib.decodeRegistryV2 | [{'row': 'TX2:204', 'status': 'CLOSED', 'function': 'crates/aspis-statement/src/pool_v1/verifier_registry.rs::decode_verifier_registry_v2', 'owner_module': 'NHY_RegistryJoin', 'roots': ['NHY_RegistryJoin.cohort']}] | MISSING-CHILD-LEMMA | Pool owner at the same argument; RuntimeEntrypointAdmission-Pool for cell identity; EnvRep for the one headline reservation |
| RSL.PoolLib.decodeEntryV1 | [{'row': 'TX2:201', 'status': 'CLOSED', 'function': 'crates/aspis-statement/src/pool_v1/verifier_registry.rs::decode_verifier_registry_entry_v1', 'owner_module': 'NJY_Roots', 'roots': ['NJY_Roots.entry', 'NJQ_Entry.source', 'NJQ_Canonical.entry_result']}] | MISSING-CHILD-LEMMA | Pool owner at the same argument; RuntimeEntrypointAdmission-Pool for cell identity; EnvRep for the one headline reservation |
| RSL.PoolLib.decodeEntryV2 | [{'row': 'TX2:202', 'status': 'CLOSED', 'function': 'crates/aspis-statement/src/pool_v1/verifier_registry.rs::decode_verifier_registry_entry_v2', 'owner_module': 'NIS_EntryJoin', 'roots': ['NIJ_EntryJoin.cohort']}] | MISSING-CHILD-LEMMA | Pool owner at the same argument; RuntimeEntrypointAdmission-Pool for cell identity; EnvRep for the one headline reservation |
| RSL.PoolLib.scanProof | [{'row': 'TX2:226', 'status': 'CLOSED', 'function': 'programs/r1-cost-probe/src/r1_pool_adapter.rs::scan_proof_buffer', 'owner_module': 'NFY_Part060', 'roots': ['NFY_NFJ_Comparison.completion', 'NFY_NFJ_Comparison.header_length', 'NFY_NFJ_Comparison.nativeEqualityBridge', 'NFY_NFJ_Comparison.same_buffer_lengths', 'NFY_NFJ_Comparison.slot_zero_iff', 'NFY_NFJ_Scanner.decode_domain', 'NFY_NFJ_Scanner.encode_domain', 'NFY_NFJ_Scanner.result_state_effects', 'NFY_NFJ_Scanner.tag_domain']}] | MISSING-CHILD-LEMMA | PCM_shared_scanProof |
| RSL.PoolLib.reconstruct | [{'row': 'TX2:224', 'status': 'CLOSED', 'function': 'programs/r1-cost-probe/src/r1_pool_adapter.rs::reconstruct_asq8_statement', 'owner_module': 'NFY_Part057', 'roots': ['NFY_NEU_CallDomains.common_packet', 'NFY_NEU_CallDomains.reached_domains', 'NFY_NEU_CallDomains.transfer_packet', 'NFY_NEU_CallDomains.transfer_reply_range', 'NFY_NEU_CallDomains.withdrawal_packet', 'NFY_NEU_CallDomains.withdrawal_reply_range', 'NFY_NEU_ReconstructAdopted.result_state_effects', 'NFY_NEU_ReconstructCore.result_state_effects']}] | MISSING-CHILD-LEMMA | PCM_shared_reconstruct |
| RSL.PoolLib.encodeStatement | [{'row': 'TX2:165', 'status': 'CLOSED', 'function': 'crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::encode_pool_v1_pair_forest_terminal_statement_v1', 'owner_module': 'NFY_Part053', 'roots': ['NFY_NEQ_EncoderOracle.result_state_effects', 'NFY_NEQ_EncoderOracle.substitution', 'NGE_NEM_EncoderReceiver.sequence_width', 'NGE_NEM_KindInstance.statement_window', 'NGE_NEQ_EncoderDomains.header_length', 'NGE_NEQ_EncoderDomains.reached_domains', 'NGE_NEQ_LateBorrow.after_preserves_child', 'NGE_NEQ_LateBorrow.poststate', 'NGE_NEQ_LateBorrow.rejoin', 'NGE_NEQ_RootFrame.array_ext', 'NGE_NEQ_RootFrame.assembled', 'NGE_NEQ_RootFrame.cover', 'NGE_NEQ_RootFrame.finish', 'NGE_NEQ_RootFrame.header_frame', 'NGE_NEQ_RootFrame.scalar_frame']}] | MISSING-CHILD-LEMMA | PCM_shared_encodeStatement |
| RSL.PoolLib.emitResult | [{'row': 'TX2:219', 'status': 'CLOSED', 'function': 'programs/r1-cost-probe/src/r1_pool_adapter.rs::emit_result', 'owner_module': 'NFY_Part058', 'roots': ['NFY_NEY_EmitComposed.encoder_bridge', 'NFY_NEY_EmitComposed.reached_encoder', 'NFY_NEY_EmitComposed.result_state_effects', 'NFY_NFD_EmitProjection.alignment0', 'NFY_NFD_EmitProjection.alignment1', 'NFY_NFD_EmitProjection.alignment2', 'NFY_NFD_EmitProjection.alignment3', 'NFY_NFD_EmitProjection.alignment4', 'NFY_NFD_EmitProjection.alignment5', 'NFY_NFD_EmitProjection.alignment6', 'NFY_NFD_EmitProjection.alignment7', 'NFY_NFD_EmitProjection.complete']}] | MISSING-CHILD-LEMMA | PCM_shared_emitResult |
| Representation.RuntimeCpiAccountView | POOL:330  | OPEN-ROW | Native/representation owner of POOL:330; not assumed by PCM |
| Representation.RuntimeReturnData | POOL:348  | OPEN-ROW | Native/representation owner of POOL:348; not assumed by PCM |
| Representation.RuntimeReturnDataClear | POOL:348  | OPEN-ROW | Native/representation owner of POOL:348; not assumed by PCM |
| Representation.RuntimeCpiReadonlyEntry7 | POOL:348  | OPEN-ROW | Native/representation owner of POOL:348; not assumed by PCM |
| Representation.RcCloneAndDrop | POOL:382  | OPEN-ROW | Native/representation owner of POOL:382; not assumed by PCM |
| Representation.ReturnedVecCapacity | POOL:348  | OPEN-ROW | Native/representation owner of POOL:348; not assumed by PCM |
| Representation.RuntimeEntryCells | POOL:328  | OPEN-ROW | Native/representation owner of POOL:328; not assumed by PCM |
| Representation.LamportCellsAndBorrow | POOL:333  | OPEN-ROW | Native/representation owner of POOL:333; not assumed by PCM |
| Representation.CpiBorrowCounterAndHandleFrame | POOL:330  | OPEN-ROW | Native/representation owner of POOL:330; not assumed by PCM |
| Representation.ReservationBinder | POOL:330  | OPEN-ROW | Native/representation owner of POOL:330; not assumed by PCM |
| VerifierCPI.330/348 | ['NMN_064.root', 'NNC_064Weak', 'NNC_BindingRoot', 'TCK_REPORT option B / Realizes / RZ-STATE'] | OPEN-ROW | Exact Pool CPI slice/entry/statement association plus Stream A selected weak/option-B top; Root0 not checked by frozen Rust |
| RSL.DeployedIds.pool |  NHJ_DeployedIds.pool_actual | MISSING-CHILD-LEMMA | PCM_Inst_Deployed |
| RSL.DeployedIds.registry |  NHJ_DeployedIds.registry_actual | MISSING-CHILD-LEMMA | PCM_Inst_Deployed |

Exact source statements, original domains, representation details and domain-discharge owners are in PCM_MAP.json. Needed-lemma names are obligations, not declarations claimed to exist. No relation/image-of-Cut is installed as a child law.

NMN_064.Domain: proofExtent=57607, checkpointExtent=1768, publicBound<=1880, Root0 checkpoint proof. Use the NNC Root0-free weak law first; derive Root0 OR the existing E_rec on the SAME realized execution; only then use NMN_064.root in the Root0 branch. Both internal Outcome bad and the outer event are E_rec, charged once.

Shared-library delivery dependency: LIB_REMAINING: shared L-star is externally ready as LIBB_PoolLib.library but its completed V0-star/weak registration is not in the provided LIB bundle; consume it read-only when exported

Target not yet established.
