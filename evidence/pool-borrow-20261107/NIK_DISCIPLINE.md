# NIK Pool borrow discipline: source/MIR review

This is a frozen-source and compiler census, not a native production-prefix certificate. All seven NIE accessor sites remain OPEN. No production inputs or transaction shapes are constructed.

Frozen revision: 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387. Stable rustc 1.94.1, optimized --release, selected Pool features r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit. NHR exact staging and frozen graph checked; lock unchanged. MIR and AST are pinned in NIK_CENSUS.json. MIR contains generic bodies; emission alone does not prove root reachability or a concrete runtime trait instantiation.

## Scope interpretation

A temporary guard survives to its temporary scope end, usually the end of its statement. A guard stored in a local, Option, branch result or Vec survives until that carrier is dropped. The inner block of an acquisition is not necessarily its lifetime. Rust nonlexical lifetimes do not shorten a RefMut destructor lifetime. Returning owned values does not alone prove all counters restored: leak/forget, splits and library effects must also be excluded. Account key inequality needs a runtime physical interpretation before it implies Rc-cell inequality. Data and lamports are separate cells.

## Functions with exclusive guards

### programs/aspis-pool/src/pair_forest.rs::process_pair_forest_deposit_with_runtime_v1

Source lines 988..1196; body SHA256 2f50e4f023ffd4325bfc208ea3ad0a1faa108458ecf19c59df55d1f9cfe5ace0.

lane_data and page_data remain live across runtime.invoke at 1170 and validate_exact_deposit_delta_v1 at 1171. The delta child borrows source/vault token data. Need SAME-cell disjointness between lane/page and those token accounts plus returning CPI borrow/frame. No claim that all counters are nonexclusive at the CPI is valid.

- Acquisition 1168; binding lane_data; statement ends 1168; lexical acquisition block [994, 1196]. Carrier escape must be reviewed independently.
- Acquisition 1169; binding page_data; statement ends 1169; lexical acquisition block [994, 1196]. Carrier escape must be reviewed independently.

MIR acquisition/drop event lines: 49904, 50388, 50393, 50428, 50433, 50523, 50527, 51784.

### programs/aspis-pool/src/pair_forest.rs::process_pair_forest_terminal_with_verifier_v1

Source lines 1615..1821; body SHA256 49900881a1301d8138c9e1589ca3821f8a0e9d21f2b40d16f4e115905dd826f5.

lane_data, page_data and marker_data remain live across optional withdrawal runtime.invoke_signed at 1792 and delta validation at 1793; later writes consume the same guards. Need exact transfer-info footprint disjointness and returning CPI frame, not a blanket no-live-guard assertion.

- Acquisition 1780; binding lane_data; statement ends 1780; lexical acquisition block [1641, 1821]. Carrier escape must be reviewed independently.
- Acquisition 1781; binding page_data; statement ends 1781; lexical acquisition block [1641, 1821]. Carrier escape must be reviewed independently.
- Acquisition 1782; binding marker_data; statement ends 1782; lexical acquisition block [1641, 1821]. Carrier escape must be reviewed independently.

MIR acquisition/drop event lines: 57990, 57995, 58000, 58059, 58064, 58069, 58168, 58172, 58176, 59543.

### programs/aspis-pool/src/pair_forest.rs::process_pair_forest_initialize_with_runtime_v1

Source lines 1994..2124; body SHA256 d0c3d69eea8be24f30dd5f7e242bc0ef6901caf31ee1199fae2a67027efe5ad4.

master_data remains live while lane_data Vec collects up to eight RefMut values at 2117. Guards escape the loop body through push; they are not dropped each iteration. Need pairwise cell distinctness and Vec-drop/error cleanup. A one-iteration invariant must track all previously collected cells.

- Acquisition 2114; binding master_data; statement ends 2114; lexical acquisition block [2000, 2124]. Carrier escape must be reviewed independently.
- Acquisition 2117; binding statement/carrier temporary; statement ends 2117; lexical acquisition block [2116, 2118]. Carrier escape must be reviewed independently.

MIR acquisition/drop event lines: 62041, 62070, 62127, 62131, 63096, 63172.

### programs/aspis-pool/src/pair_forest.rs::process_pair_forest_checkpoint_with_runtime_v1

Source lines 2130..2188; body SHA256 e4d2e5e038943e4d512f0d447ea0946d9e3aa1a956a613655a32831e38247d81.

master_data remains live during checkpoint acquisition; both survive the two copy operations through function return. Need distinct cell admission for simultaneous acquisition; writes use borrowed slices rather than reborrow account data.

- Acquisition 2183; binding master_data; statement ends 2183; lexical acquisition block [2136, 2188]. Carrier escape must be reviewed independently.
- Acquisition 2184; binding checkpoint_data; statement ends 2184; lexical acquisition block [2136, 2188]. Carrier escape must be reviewed independently.

MIR acquisition/drop event lines: 63999, 64034, 64038, 64519, 64583.

### programs/aspis-pool/src/pair_processor.rs::process_pair_private_transfer_with_verifier_v1

Source lines 277..409; body SHA256 d8e4488bf5a96136e7911d402415c107ffcd37b07f2239b3c146b134a868ab8c.

The rollover/new-page guard is a statement temporary. The else-arm current_data is scoped through append_roots_unchecked. Later pool/marker copy temporaries end at their statements; checkpoint logging and set_return_data are not account-data accessors. Need child slice footprint/Drop laws and alias frame.

- Acquisition 383; binding statement/carrier temporary; statement ends 388; lexical acquisition block [380, 389]. Carrier escape must be reviewed independently.
- Acquisition 391; binding current_data; statement ends 391; lexical acquisition block [389, 397]. Carrier escape must be reviewed independently.
- Acquisition 399; binding statement/carrier temporary; statement ends 400; lexical acquisition block [300, 409]. Carrier escape must be reviewed independently.
- Acquisition 402; binding statement/carrier temporary; statement ends 404; lexical acquisition block [300, 409]. Carrier escape must be reviewed independently.

MIR acquisition/drop event lines: 75488, 75526, 75695, 75699, 75703, 75707, 76572, 76650.

### programs/aspis-pool/src/pair_processor.rs::process_pair_withdrawal_with_verifier_v1

Source lines 418..587; body SHA256 822cb7bd0a9059d88a307ab3df751ce4ca28a8c2ff596c6fd0faec3663e839a6.

history_data escapes the if-expression into a function-scope local. It and pool_data/marker_data remain live across runtime.invoke_signed at 554 and validate_exact_withdrawal_delta_v1 at 560. Need SAME-cell footprint exclusion against vault/destination/authority and CPI post-state. Source key/layout checks require physical interpretation.

- Acquisition 543; binding history_data; statement ends 546; lexical acquisition block [542, 544]. Carrier escape must be reviewed independently.
- Acquisition 545; binding history_data; statement ends 546; lexical acquisition block [544, 546]. Carrier escape must be reviewed independently.
- Acquisition 547; binding pool_data; statement ends 547; lexical acquisition block [443, 587]. Carrier escape must be reviewed independently.
- Acquisition 548; binding marker_data; statement ends 548; lexical acquisition block [443, 587]. Carrier escape must be reviewed independently.

MIR acquisition/drop event lines: 78660, 78796, 78801, 78806, 78851, 78856, 78861, 78932, 78936, 78940.

### programs/aspis-pool/src/processor.rs::close_program_account_v1

Source lines 236..271; body SHA256 1e8f76fb3aecac099c5b160722de97da2c9145555ccafa7ca728a986b0e17d22.

The data fill guard is a statement temporary, ending before lamports() at 258. Destination/account lamports guards coexist inside block 259..267 and drop before assign/resize. Need refund/source cell distinctness for acquisition and data temporary Drop; lamports and data are separate cells.

- Acquisition 257; binding statement/carrier temporary; statement ends 257; lexical acquisition block [241, 271]. Carrier escape must be reviewed independently.
- Acquisition 260; binding destination_lamports; statement ends 260; lexical acquisition block [259, 267]. Carrier escape must be reviewed independently.
- Acquisition 261; binding account_lamports; statement ends 261; lexical acquisition block [259, 267]. Carrier escape must be reviewed independently.

MIR acquisition/drop event lines: 122632, 122724, 122750, 122763, 122773, 122873, 123075, 123112.

### programs/aspis-pool/src/processor.rs::process_prepare_settlement_with_runtime_v1

Source lines 1167..1349; body SHA256 a627354180441754744d7d57498792e8d4721d6587890ea347d8e99fcf9fe3df.

core_plan and each optional shard copy use statement temporaries, with no accessor or CPI between acquisition and matching statement cleanup. Need native copy/error/Drop association and shared-entry frame; loop iterations must preserve all other cells.

- Acquisition 1340; binding statement/carrier temporary; statement ends 1342; lexical acquisition block [1175, 1349]. Carrier escape must be reviewed independently.
- Acquisition 1344; binding statement/carrier temporary; statement ends 1346; lexical acquisition block [1343, 1347]. Carrier escape must be reviewed independently.

MIR acquisition/drop event lines: 137215, 137219, 137989, 138073.

### programs/aspis-pool/src/processor.rs::process_settle_prepared_with_runtime_v1

Source lines 1674..1910; body SHA256 20e872edd4accc1853ebed98110b0a375209e2d56f98653b3d2f5df9f342f531.

Explicit drops of authorization/source-next/current/pool shared guards precede CPI. core_data and shard_data remain until explicit drops at 1892/1893 before close calls. Data copies are statement temporaries; marker and history aliases with surviving shared plan guards still need exclusion. Borrow scopes are not equivalent to a universal zero-counter invariant.

- Acquisition 1873; binding statement/carrier temporary; statement ends 1874; lexical acquisition block [1687, 1910]. Carrier escape must be reviewed independently.
- Acquisition 1876; binding statement/carrier temporary; statement ends 1878; lexical acquisition block [1875, 1879]. Carrier escape must be reviewed independently.
- Acquisition 1881; binding statement/carrier temporary; statement ends 1884; lexical acquisition block [1687, 1910]. Carrier escape must be reviewed independently.
- Acquisition 1885; binding statement/carrier temporary; statement ends 1887; lexical acquisition block [1687, 1910]. Carrier escape must be reviewed independently.

MIR acquisition/drop event lines: 144343, 144901, 144905, 144909, 144913, 144956, 144960, 144964, 144968, 144972, 144976, 144980, 144988, 144996, 145004, 145012, 145020, 145517, 145643, 145678, 145791, 145818, 146018, 146026, 146044, 146052, 146210, 146341, 146418, 146495, 146573, 146643, 146712, 146746, 146816, 146830, 146887, 146921.

### programs/aspis-pool/src/processor.rs::create_and_write_marker_v1

Source lines 1983..2020; body SHA256 cab4e60f266ed6b539c8ecb4353636ca1354594ec65eaff2dba2e683f266194e.

The marker data guard follows creation/address children and survives only its copy and function return; no later account accessor/CPI is lexical in this scope. Need source prefix/CPI frame and SDK Drop association.

- Acquisition 2017; binding data; statement ends 2017; lexical acquisition block [1991, 2020]. Carrier escape must be reviewed independently.

MIR acquisition/drop event lines: 148228, 148398.

### programs/aspis-pool/src/processor.rs::process_withdrawal_with_runtime_v1

Source lines 2189..2377; body SHA256 a050053eccce91ab7a059de58f97e044e1d230052bf1f2ca1e09ef2b49ee9e43.

The marker copy temporary follows successful custody CPI inside the before_persist callback. The enclosing transition helper holds pool/current/next guards during that callback. Need callback footprint and alias admission; a local no-RefMut-before-CPI argument would omit guards held by the parent.

- Acquisition 2357; binding statement/carrier temporary; statement ends 2359; lexical acquisition block [2315, 2361]. Carrier escape must be reviewed independently.

MIR acquisition/drop event lines: 153791, 153901, 154239.

### programs/aspis-pool/src/transition.rs::initialize_pool_accounts_v1

Source lines 567..610; body SHA256 7c4c63c5d43c012fd9d399862ea1bb4766512055327e53370f6e04039e14ac05.

pool_data survives acquisition of page_data; owned mutable slices are passed to encoding/page-write children. Need cell distinctness and child no-escape/frame laws; both guards clean up on error/return.

- Acquisition 596; binding pool_data; statement ends 596; lexical acquisition block [571, 610]. Carrier escape must be reviewed independently.
- Acquisition 600; binding page_data; statement ends 600; lexical acquisition block [571, 610]. Carrier escape must be reviewed independently.

MIR acquisition/drop event lines: 180365, 180434, 180442, 180486, 180491, 180506, 180538, 180542, 180550.

### programs/aspis-pool/src/transition.rs::apply_authorized_append_after_checked_state_v1

Source lines 620..752; body SHA256 85af31393162401d597edd4cfff33771c7505f4f6cdb9f8a9af9db7eaa6b4f85.

pool_data plus optional current_data and next_data are all live at before_persist at 735. The callback can CPI and access marker data (withdrawal parent). This is a real cross-function guard-carrying edge. Must prove callback touched-cell footprint disjoint from held data cells on the actual layout. A guard-free child-call invariant is false as stated.

- Acquisition 722; binding pool_data; statement ends 722; lexical acquisition block [632, 752]. Carrier escape must be reviewed independently.
- Acquisition 727; binding current_data; statement ends 730; lexical acquisition block [726, 728]. Carrier escape must be reviewed independently.
- Acquisition 732; binding next_data; statement ends 734; lexical acquisition block [632, 752]. Carrier escape must be reviewed independently.

MIR acquisition/drop event lines: 182653, 182658, 182663, 182681, 182690, 182719, 182723, 182727, 183470.

## Every emitted Pool function

Every emitted source function is listed below. `no local exclusive acquisition` is a source fact only: entry guards, alias frames, returning children and shared saturation remain obligations. Full per-call sites, owner-field checks, source SHA and MIR location are in NIK_CENSUS.json.

- programs/aspis-pool/src/anchor.rs::PrevalidatedHistoricalAnchorV1::authenticated: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/anchor.rs::PrevalidatedHistoricalAnchorV1::history_page: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/anchor.rs::PrevalidatedHistoricalAnchorV1::header: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/anchor.rs::load_canonical_pool_state: no local exclusive acquisition; shared=1; accessors=0; CPI=0.
- programs/aspis-pool/src/anchor.rs::bind_envelope_to_state_and_selection: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/anchor.rs::require_history_page_privileges: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/anchor.rs::authenticate_historical_anchor_against_state_v1: no local exclusive acquisition; shared=1; accessors=0; CPI=0.
- programs/aspis-pool/src/anchor.rs::authenticate_historical_anchor_after_prevalidated_state_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/anchor.rs::authenticate_historical_anchor_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/cancel_prepared_settlement_instruction.rs::CancelPreparedSettlementAccountShapeV1::account_count: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/cancel_prepared_settlement_instruction.rs::CancelPreparedSettlementAccountShapeV1::has_rollover_shard: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/cancel_prepared_settlement_instruction.rs::ProgramError::from: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/cancel_prepared_settlement_instruction.rs::decode_cancel_prepared_settlement_instruction_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/cancel_prepared_settlement_instruction.rs::encode_cancel_prepared_settlement_instruction_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/deposit.rs::digest_is_canonical: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/deposit.rs::validate_request: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/deposit.rs::load_pool_state_for_deposit: no local exclusive acquisition; shared=1; accessors=0; CPI=0.
- programs/aspis-pool/src/deposit.rs::require_disjoint_account_groups: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/deposit.rs::prepare_deposit_after_state_validation_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/deposit.rs::finish_deposit_event_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/deposit.rs::apply_vault_backed_deposit_with_transfer_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/deposit.rs::apply_prevalidated_vault_backed_deposit_with_transfer_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/deposit.rs::apply_vault_backed_deposit_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/deposit.rs::apply_prevalidated_vault_backed_deposit_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/deposit_transport.rs::DepositInstructionDataV1::as_bytes: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/deposit_transport.rs::DepositEventReturnDataV1::as_bytes: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/deposit_transport.rs::digest_is_canonical: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/deposit_transport.rs::encode_deposit_instruction_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/deposit_transport.rs::decode_deposit_instruction_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/deposit_transport.rs::decode_deposit_instruction_with_magic_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/deposit_transport.rs::encode_deposit_event_return_data_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/deposit_transport.rs::execute_and_emit_deposit_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/deposit_transport.rs::process_vault_backed_deposit_instruction_with_runtime_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/deposit_transport.rs::process_vault_backed_deposit_instruction_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/deposit_transport.rs::process_prevalidated_vault_backed_deposit_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/error.rs::ProgramError::from: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/history.rs::pool_v1_root_page_address: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/history.rs::digest_is_canonical: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/history.rs::require_program_account: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/history.rs::require_program_owned: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/history.rs::require_root_page_address: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/history.rs::require_root_page_address_with_bump: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/history.rs::validate_root_page_bytes: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/history.rs::read_retained_root: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/history.rs::write_new_page_unchecked: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/history.rs::append_roots_unchecked: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/history.rs::validate_new_page_account: no local exclusive acquisition; shared=1; accessors=0; CPI=0.
- programs/aspis-pool/src/instruction.rs::ProgramError::from: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/instruction.rs::PoolInstructionFormatErrorV1::from: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/instruction.rs::digest_is_canonical: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/instruction.rs::exact_array: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/instruction.rs::require_exact_header: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/instruction.rs::decode_statement_common: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/instruction.rs::require_envelope_statement_match: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/instruction.rs::encode_initialize_instruction_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/instruction.rs::decode_initialize_instruction_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/instruction.rs::encode_statement_common: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/instruction.rs::encode_private_transfer_instruction_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/instruction.rs::encode_pair_private_transfer_instruction_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/instruction.rs::decode_private_transfer_instruction_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/instruction.rs::decode_pair_private_transfer_instruction_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/instruction.rs::decode_private_transfer_with_magic_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/instruction.rs::encode_withdrawal_instruction_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/instruction.rs::encode_pair_withdrawal_instruction_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/instruction.rs::decode_withdrawal_instruction_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/instruction.rs::decode_pair_withdrawal_instruction_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/instruction.rs::decode_withdrawal_with_magic_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/instruction.rs::decode_deposit_top_level_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/instruction.rs::encode_initialization_receipt_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/instruction.rs::encode_transition_receipt_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/nullifier.rs::pool_v1_nullifier_marker_address: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/nullifier.rs::pack_pool_v1_pair_forest_marker_seed_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/nullifier.rs::pool_v1_pair_forest_marker_seed_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/nullifier.rs::pool_v1_pair_forest_marker_seed_str_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/nullifier.rs::pool_v1_pair_forest_nullifier_marker_address: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/nullifier.rs::PlannedNullifierMarkerV1::preparation: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/nullifier.rs::PlannedNullifierMarkerV1::address_bump: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/nullifier.rs::PlannedNullifierMarkerV1::marker: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/nullifier.rs::PlannedNullifierMarkerV1::encoded_marker: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/nullifier.rs::plan_nullifier_marker_consumption_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/nullifier.rs::classify_nullifier_marker_account_v1: no local exclusive acquisition; shared=1; accessors=1; CPI=0.
- programs/aspis-pool/src/nullifier.rs::PlannedPairForestNullifierMarkerV1::preparation: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/nullifier.rs::PlannedPairForestNullifierMarkerV1::seed: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/nullifier.rs::PlannedPairForestNullifierMarkerV1::encoded_marker: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/nullifier.rs::plan_pair_forest_nullifier_marker_consumption_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/nullifier.rs::recheck_pair_forest_nullifier_marker_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_dispatch.rs::pair_cu_checkpoint: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_dispatch.rs::AuthenticatedPairAfterstateV1::value: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_dispatch.rs::authenticate_pair_verified_afterstate_return_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_dispatch.rs::SolanaPairVerifierRuntimeV1::clear_return_data: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_dispatch.rs::SolanaPairVerifierRuntimeV1::invoke: no local exclusive acquisition; shared=0; accessors=0; CPI=1.
- programs/aspis-pool/src/pair_dispatch.rs::SolanaPairVerifierRuntimeV1::get_return_data: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_dispatch.rs::supported_loader: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_dispatch.rs::require_verifier_program: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_dispatch.rs::derive_pair_verifier_account_claim_v1: no local exclusive acquisition; shared=1; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_dispatch.rs::plan_pair_verifier_dispatch_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_dispatch.rs::invoke_pair_verifier_with_runtime_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=1.
- programs/aspis-pool/src/pair_dispatch.rs::invoke_pair_afterstate_verifier_with_runtime_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=1.
- programs/aspis-pool/src/pair_dispatch.rs::dispatch_pair_verifier_readonly_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest.rs::PoolV1PairForestTerminalBumpHintsV1::encode: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest.rs::PoolV1PairForestTerminalBumpHintsV1::vault: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest.rs::split_pair_forest_terminal_bump_hints_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest.rs::pool_v1_pair_forest_terminal_bump_hints_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest.rs::encode_pair_forest_terminal_instruction_data_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest.rs::encode_pair_forest_initialize_instruction_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest.rs::decode_pair_forest_initialize_instruction_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest.rs::encode_pair_forest_checkpoint_instruction_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest.rs::decode_pair_forest_checkpoint_instruction_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest.rs::encode_pair_forest_deposit_instruction_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest.rs::decode_pair_forest_deposit_instruction_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest.rs::pool_v1_pair_forest_global_root_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest.rs::pool_v1_pair_forest_master_address: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest.rs::pool_v1_pair_forest_lane_address: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest.rs::pool_v1_pair_forest_checkpoint_address: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest.rs::pool_v1_pair_forest_lane_root_page_address: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest.rs::require_exact_account_count: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest.rs::require_forest_mint_account: no local exclusive acquisition; shared=1; accessors=1; CPI=0.
- programs/aspis-pool/src/pair_forest.rs::require_program_owned_zeroed: no local exclusive acquisition; shared=1; accessors=1; CPI=0.
- programs/aspis-pool/src/pair_forest.rs::genesis_lane_state: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest.rs::decode_master_account: no local exclusive acquisition; shared=1; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest.rs::master_address_matches: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest.rs::lane_address_matches: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest.rs::stored_lane_bump: no local exclusive acquisition; shared=1; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest.rs::decode_lane_account: no local exclusive acquisition; shared=1; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest.rs::decode_lane_account_from_program_invariant_v1: no local exclusive acquisition; shared=1; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest.rs::encode_lane_from_authenticated_result_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest.rs::require_alias_free: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest.rs::decode_checkpoint_master_box_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest.rs::decode_checkpoint_lanes_box_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest.rs::plan_pair_forest_checkpoint_accounts_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest.rs::account_is_zeroed_program_page: no local exclusive acquisition; shared=1; accessors=1; CPI=0.
- programs/aspis-pool/src/pair_forest.rs::validate_lane_current_page: no local exclusive acquisition; shared=1; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest.rs::prepare_deposit_append_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest.rs::decode_deposit_lane_box_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest.rs::process_pair_forest_deposit_with_runtime_v1: exclusive-scope review above; shared=0; accessors=1; CPI=1.
- programs/aspis-pool/src/pair_forest.rs::plan_pair_forest_spend_layout_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest.rs::validate_pair_forest_request_accounts_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest.rs::next_pair_forest_lane_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest.rs::decode_terminal_request_box_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest.rs::decode_terminal_master_box_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest.rs::decode_terminal_checkpoint_box_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest.rs::decode_terminal_lane_box_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest.rs::terminal_common_box_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest.rs::transfer_terminal_statement_box_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest.rs::withdrawal_terminal_statement_box_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest.rs::validate_authenticated_terminal_result_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest.rs::next_lane_image_box_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest.rs::terminal_result_bytes_box_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest.rs::process_pair_forest_terminal_with_verifier_v1: exclusive-scope review above; shared=0; accessors=0; CPI=1.
- programs/aspis-pool/src/pair_forest.rs::process_pair_forest_terminal_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest.rs::decode_forest_initialization_box_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest.rs::forest_master_image_box_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest.rs::genesis_lane_image_box_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest.rs::process_pair_forest_initialize_with_runtime_v1: exclusive-scope review above; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest.rs::process_pair_forest_checkpoint_with_runtime_v1: exclusive-scope review above; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest.rs::decode_retained_pair_forest_checkpoint_account_v1: no local exclusive acquisition; shared=1; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest_dispatch.rs::AuthenticatedPairForestResultV1::value: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest_dispatch.rs::AuthenticatedPairForestResultV1::exact_bytes: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest_dispatch.rs::supported_loader: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest_dispatch.rs::require_verifier_program: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest_dispatch.rs::proof_transport_verifier: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest_dispatch.rs::require_checkpoint_distinct: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest_dispatch.rs::plan_pair_forest_terminal_dispatch_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest_dispatch.rs::plan_pair_forest_terminal_dispatch_with_bytes_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest_dispatch.rs::SolanaPairForestVerifierRuntimeV1::clear_return_data: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest_dispatch.rs::SolanaPairForestVerifierRuntimeV1::invoke: no local exclusive acquisition; shared=0; accessors=0; CPI=1.
- programs/aspis-pool/src/pair_forest_dispatch.rs::SolanaPairForestVerifierRuntimeV1::get_return_data: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_forest_dispatch.rs::invoke_pair_forest_terminal_with_runtime_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=1.
- programs/aspis-pool/src/pair_forest_dispatch.rs::dispatch_pair_forest_terminal_readonly_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_processor.rs::pair_cu_checkpoint: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_processor.rs::require_unique: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_processor.rs::plan_layout: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_processor.rs::validate_history: no local exclusive acquisition; shared=3; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_processor.rs::process_pair_private_transfer_with_verifier_v1: exclusive-scope review above; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_processor.rs::process_pair_withdrawal_with_verifier_v1: exclusive-scope review above; shared=0; accessors=0; CPI=1.
- programs/aspis-pool/src/pair_state.rs::exact: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_state.rs::pool_v1_pair_state_address: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_state.rs::CanonicalPairPoolStateV1::deref: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_state.rs::CanonicalPairPoolStateV1::decode_account_from_program_invariant: no local exclusive acquisition; shared=1; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_state.rs::CanonicalPairPoolStateV1::require_same_account: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_state.rs::PairPoolStateV1::genesis: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_state.rs::PairPoolStateV1::current_root_sequence: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_state.rs::PairPoolStateV1::apply_authenticated_afterstate_from_program_invariant: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_state.rs::PairPoolStateV1::append_occupied_pair_from_program_invariant: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_state.rs::PairPoolStateV1::append_verified_pair_from_program_invariant: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_state.rs::PairPoolStateV1::write_encoding_prevalidated: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_state.rs::PairPoolStateV1::encode: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/pair_state.rs::PairPoolStateV1::decode_from_program_invariant: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/prepared_settlement.rs::AuthenticatedPreparedSettlementActionV1::transition_kind: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/prepared_settlement.rs::AuthenticatedPreparedSettlementActionV1::withdrawal_amount_and_destination: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/prepared_settlement.rs::AuthenticatedPreparedSettlementActionV1::ordered_commitments: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/prepared_settlement.rs::CanonicalSettlementStatementV1::transition_kind: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/prepared_settlement.rs::CanonicalSettlementStatementV1::pool: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/prepared_settlement.rs::CanonicalSettlementStatementV1::deployment_domain: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/prepared_settlement.rs::CanonicalSettlementStatementV1::anchor_sequence: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/prepared_settlement.rs::CanonicalSettlementStatementV1::anchor_root: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/prepared_settlement.rs::CanonicalSettlementStatementV1::nullifier: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/prepared_settlement.rs::CanonicalSettlementStatementV1::asset_id: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/prepared_settlement.rs::CanonicalSettlementStatementV1::ordered_commitments: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/prepared_settlement.rs::pool_v1_authorization_receipt_account_address: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/prepared_settlement.rs::decode_canonical_statement: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/prepared_settlement.rs::authenticate_statement_and_receipt_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/prepared_settlement.rs::verifier_selection_from_receipt: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/prepared_settlement.rs::authenticated_selection_matches_receipt: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/prepared_settlement.rs::authenticate_prepared_settlement_receipt_claim_v1: no local exclusive acquisition; shared=1; accessors=0; CPI=0.
- programs/aspis-pool/src/prepared_settlement.rs::checked_history_distribution: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/prepared_settlement.rs::zeroed_page_box: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/prepared_settlement.rs::build_prepared_settlement_plan_v1: no local exclusive acquisition; shared=4; accessors=0; CPI=0.
- programs/aspis-pool/src/prepared_settlement.rs::request_transition_kind: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/prepared_settlement.rs::request_commitments: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/prepared_settlement.rs::append_roots: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/prepared_settlement.rs::validate_receipt_progression: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/prepared_settlement.rs::source_state_and_result_image_match: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/prepared_settlement.rs::history_result_images_match: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/prepared_settlement.rs::nullifier_marker_matches: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/prepared_settlement.rs::apply_prepared_settlement_plan_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/prepared_settlement.rs::authorize_prepared_settlement_plan_close_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/prepared_settlement_format.rs::ProgramError::from: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/prepared_settlement_format.rs::pool_v1_prepared_settlement_plan_address: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/prepared_settlement_format.rs::pool_v1_prepared_settlement_rollover_address: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/prepared_settlement_format.rs::exact_image_digest_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/prepared_settlement_format.rs::exact_array: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/prepared_settlement_format.rs::exact_ref: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/prepared_settlement_format.rs::zeroed_box: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/prepared_settlement_format.rs::transition_kind_from_byte: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/prepared_settlement_format.rs::receipt_is_exact: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/prepared_settlement_format.rs::encode_receipt: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/prepared_settlement_format.rs::decode_receipt: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/prepared_settlement_format.rs::digest32: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/prepared_settlement_format.rs::encode_rollover_shard_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/prepared_settlement_format.rs::encode_prepared_settlement_plan_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/prepared_settlement_format.rs::decode_rollover_shard_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/prepared_settlement_format.rs::decode_prepared_settlement_plan_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/prepared_settlement_instruction.rs::ProgramError::from: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/prepared_settlement_instruction.rs::exact_array: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/prepared_settlement_instruction.rs::transition_kind: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/prepared_settlement_instruction.rs::validate_nested_spend: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/prepared_settlement_instruction.rs::decode_prepare_settlement_instruction_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/prepared_settlement_instruction.rs::encode_prepare_settlement_instruction_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/processor.rs::SolanaPoolCpiRuntimeV1::invoke: no local exclusive acquisition; shared=0; accessors=0; CPI=1.
- programs/aspis-pool/src/processor.rs::SolanaPoolCpiRuntimeV1::invoke_signed: no local exclusive acquisition; shared=0; accessors=0; CPI=1.
- programs/aspis-pool/src/processor.rs::solana_sha256: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/processor.rs::supported_program_loader: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/processor.rs::require_unique_accounts: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/processor.rs::require_payer_and_system_program: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/processor.rs::close_program_account_v1: exclusive-scope review above; shared=0; accessors=2; CPI=0.
- programs/aspis-pool/src/processor.rs::plan_fresh_program_pda: no local exclusive acquisition; shared=1; accessors=1; CPI=0.
- programs/aspis-pool/src/processor.rs::create_or_allocate_pda: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/processor.rs::create_or_allocate_pda_with_rent: no local exclusive acquisition; shared=0; accessors=3; CPI=4.
- programs/aspis-pool/src/processor.rs::create_or_allocate_with_seed_with_rent: no local exclusive acquisition; shared=0; accessors=3; CPI=4.
- programs/aspis-pool/src/processor.rs::require_token_program_account: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/processor.rs::require_initialized_empty_vault: no local exclusive acquisition; shared=1; accessors=0; CPI=0.
- programs/aspis-pool/src/processor.rs::plan_vault_initialization: no local exclusive acquisition; shared=0; accessors=1; CPI=0.
- programs/aspis-pool/src/processor.rs::initialize_vault_account: no local exclusive acquisition; shared=0; accessors=0; CPI=1.
- programs/aspis-pool/src/processor.rs::load_canonical_pool_state: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/processor.rs::create_program_pda_if_needed: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/processor.rs::require_fresh_rent_exempt_program_pda: no local exclusive acquisition; shared=0; accessors=2; CPI=0.
- programs/aspis-pool/src/processor.rs::process_initialize_with_runtime_v1: no local exclusive acquisition; shared=1; accessors=0; CPI=0.
- programs/aspis-pool/src/processor.rs::deposit_rolls_to_next_page: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/processor.rs::process_deposit_with_runtime_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/processor.rs::require_spend_capacity: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/processor.rs::plan_spend_page_layout_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/processor.rs::validate_spend_binding_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/processor.rs::decode_prepare_settlement_request_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/processor.rs::plan_prepare_settlement_page_layout_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/processor.rs::create_prepare_rollover_page_if_needed: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/processor.rs::process_prepare_settlement_with_runtime_v1: exclusive-scope review above; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/processor.rs::plan_settle_prepared_layout_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/processor.rs::require_prepared_plan_account_v1: no local exclusive acquisition; shared=0; accessors=1; CPI=0.
- programs/aspis-pool/src/processor.rs::process_cancel_prepared_settlement_with_runtime_v1: no local exclusive acquisition; shared=2; accessors=0; CPI=0.
- programs/aspis-pool/src/processor.rs::create_nullifier_marker_if_needed_v1: no local exclusive acquisition; shared=0; accessors=1; CPI=0.
- programs/aspis-pool/src/processor.rs::create_pair_forest_nullifier_marker_if_needed_v1: no local exclusive acquisition; shared=0; accessors=1; CPI=0.
- programs/aspis-pool/src/processor.rs::process_settle_prepared_with_runtime_v1: exclusive-scope review above; shared=6; accessors=0; CPI=1.
- programs/aspis-pool/src/processor.rs::plan_marker_from_envelope_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/processor.rs::create_next_root_page_if_needed: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/processor.rs::state_accounts_for_append_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/processor.rs::create_and_write_marker_v1: exclusive-scope review above; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/processor.rs::process_private_transfer_with_runtime_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/processor.rs::process_withdrawal_with_runtime_v1: exclusive-scope review above; shared=0; accessors=0; CPI=1.
- programs/aspis-pool/src/processor.rs::dispatch_selected_verifier_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/processor.rs::process_instruction: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/registry.rs::pool_v1_verifier_registry_address: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/registry.rs::pool_v1_verifier_entry_address: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/registry.rs::pool_v1_verifier_registry_v2_address: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/registry.rs::pool_v1_verifier_entry_v2_address: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/registry.rs::AuthenticatedVerifierSelectionV1::matches_policy: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/registry.rs::AuthenticatedVerifierSelectionV1::matches: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/registry.rs::AuthenticatedVerifierSelectionV1::registry_generation: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/registry.rs::AuthenticatedVerifierSelectionV1::authenticated_at_slot: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/registry.rs::AuthenticatedVerifierSelectionV1::matches_verifier_owner: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/registry.rs::require_readonly_registry_account: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/registry.rs::authenticate_verifier_selection_v1: no local exclusive acquisition; shared=2; accessors=0; CPI=0.
- programs/aspis-pool/src/registry.rs::stored_bump_address_matches: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/registry.rs::authenticate_verifier_selection_v2: no local exclusive acquisition; shared=2; accessors=0; CPI=0.
- programs/aspis-pool/src/settle_prepared_instruction.rs::ProgramError::from: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/settle_prepared_instruction.rs::transition_kind: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/settle_prepared_instruction.rs::validate_statement: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/settle_prepared_instruction.rs::decode_settle_prepared_instruction_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/settle_prepared_instruction.rs::encode_settle_prepared_instruction_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/state.rs::exact_state_array: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/state.rs::pool_v1_state_address: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/state.rs::CanonicalPoolStateV1::decode_account: no local exclusive acquisition; shared=1; accessors=0; CPI=0.
- programs/aspis-pool/src/state.rs::CanonicalPoolStateV1::decode_account_from_program_invariant: no local exclusive acquisition; shared=1; accessors=0; CPI=0.
- programs/aspis-pool/src/state.rs::CanonicalPoolStateV1::require_same_writable_account: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/state.rs::CanonicalPoolStateV1::as_state: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/state.rs::CanonicalPoolStateV1::reconstructed_tree: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/state.rs::CanonicalPoolStateV1::deref: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/state.rs::PoolStateV1::genesis: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/state.rs::PoolStateV1::current_root_sequence: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/state.rs::PoolStateV1::genesis_boxed: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/state.rs::PoolStateV1::decode_boxed: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/state.rs::PoolStateV1::decode_boxed_with_validated_tree: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/state.rs::PoolStateV1::decode_boxed_from_program_invariant: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/state.rs::PoolStateV1::validate_encoding: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/state.rs::PoolStateV1::write_encoding_prevalidated: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/state.rs::PoolStateV1::encode: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/state.rs::PoolStateV1::decode_with_validated_tree: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/state.rs::PoolStateV1::decode_from_program_invariant: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/state.rs::PoolStateV1::decode: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/transition.rs::AuthorizedAppendV1::count: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/transition.rs::AuthorizedAppendV1::validate_leaves: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/transition.rs::PrevalidatedNewHistoryPageV1::require_matches: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/transition.rs::prevalidate_new_history_page_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/transition.rs::PrevalidatedCurrentHistoryV1::require_matches: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/transition.rs::AuthorizedSourceStateV1<'a>::as_state: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/transition.rs::AuthorizedSourceStateV1<'a>::prepare: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/transition.rs::PreparedAuthorizedAppendV1::validate_inherited_state_and_cursor: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/transition.rs::map_tree_error: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/transition.rs::prepare_checked_append: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/transition.rs::prepare_append_from_canonical_state: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/transition.rs::append_one_from_program_invariant: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/transition.rs::prepare_authorized_append_images_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/transition.rs::validate_current_history: no local exclusive acquisition; shared=1; accessors=0; CPI=0.
- programs/aspis-pool/src/transition.rs::validate_current_history_after_prevalidated_anchor_v1: no local exclusive acquisition; shared=1; accessors=0; CPI=0.
- programs/aspis-pool/src/transition.rs::initialize_pool_accounts_v1: exclusive-scope review above; shared=1; accessors=0; CPI=0.
- programs/aspis-pool/src/transition.rs::apply_authorized_append_after_checked_state_v1: exclusive-scope review above; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/transition.rs::apply_authorized_append_after_prevalidated_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/transition.rs::apply_authorized_append_after_prevalidated_history_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/transition.rs::apply_authorized_append_after_v1: no local exclusive acquisition; shared=1; accessors=0; CPI=0.
- programs/aspis-pool/src/vault.rs::pool_v1_vault_authority_address: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/vault.rs::pool_v1_vault_token_account_address: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/vault.rs::require_zero: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/vault.rs::token_array: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/vault.rs::parse_coption_pubkey: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/vault.rs::parse_coption_u64: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/vault.rs::parse_legacy_mint_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/vault.rs::parse_legacy_token_account_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/vault.rs::require_token_owned_account: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/vault.rs::exact_five_accounts: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/vault.rs::plan_legacy_deposit_transfer_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/vault.rs::plan_legacy_deposit_transfer_from_identity_v1: no local exclusive acquisition; shared=3; accessors=0; CPI=0.
- programs/aspis-pool/src/vault.rs::exact_transfer_account_infos_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/vault.rs::exact_five_withdrawal_accounts: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/vault.rs::plan_legacy_withdrawal_transfer_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/vault.rs::plan_legacy_withdrawal_transfer_from_identity_v1: no local exclusive acquisition; shared=3; accessors=1; CPI=0.
- programs/aspis-pool/src/vault.rs::exact_withdrawal_transfer_account_infos_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/vault.rs::validate_exact_withdrawal_delta_v1: no local exclusive acquisition; shared=2; accessors=0; CPI=0.
- programs/aspis-pool/src/vault.rs::validate_exact_deposit_delta_v1: no local exclusive acquisition; shared=2; accessors=0; CPI=0.
- programs/aspis-pool/src/verifier_dispatch.rs::derive_verifier_dispatch_claim_v1: no local exclusive acquisition; shared=1; accessors=0; CPI=0.
- programs/aspis-pool/src/verifier_dispatch.rs::AuthenticatedVerifierDispatchV1::plan: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/verifier_dispatch.rs::SolanaVerifierDispatchRuntimeV1::clear_return_data: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/verifier_dispatch.rs::SolanaVerifierDispatchRuntimeV1::invoke: no local exclusive acquisition; shared=0; accessors=0; CPI=1.
- programs/aspis-pool/src/verifier_dispatch.rs::SolanaVerifierDispatchRuntimeV1::get_return_data: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/verifier_dispatch.rs::supported_verifier_loader: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/verifier_dispatch.rs::require_selected_verifier_program_account: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/verifier_dispatch.rs::authenticate_proof_account_body_v1: no local exclusive acquisition; shared=1; accessors=0; CPI=0.
- programs/aspis-pool/src/verifier_dispatch.rs::plan_authenticated_verifier_dispatch_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/verifier_dispatch.rs::authenticate_verifier_return_data_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/verifier_dispatch.rs::require_exact_readonly_cpi_accounts_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/verifier_dispatch.rs::invoke_freshly_planned_verifier_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=1.
- programs/aspis-pool/src/verifier_dispatch.rs::dispatch_authenticated_verifier_readonly_with_runtime_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
- programs/aspis-pool/src/verifier_dispatch.rs::dispatch_authenticated_verifier_readonly_v1: no local exclusive acquisition; shared=0; accessors=0; CPI=0.
