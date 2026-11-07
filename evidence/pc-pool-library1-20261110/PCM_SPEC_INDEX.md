# PCM canonical specification source set

FROZEN source set for stage 1. These are specification/reference models and rejection checks, not native proofs or row candidates. No parent consumes this output; no Pool row credit.

Pool b936275465600469312d1f058cdc91ea2a11f3dc; crates/lock 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387. Source and mutable proof parameters are distinguished: every Child law must be the prescribed SAME-argument deterministic CLOSED model graph, with its original domain. Until installed, every theorem is supporting work under (bp)(3).

RSL_Pool.PoolLib is reused literally via PCM.SharedPoolLib. All its fields remain unchanged. PCM account/statement/result views require the adapters listed in the slot map.

Account slices cover every count and aliasing shape; successful count checks select the finite admitted layouts (c-c). Native account/cell identity is supplied ONLY by RuntimeEntrypointAdmission-Pool: valid, freshGuards, noExternalBorrows, liveAccount, counterZero, sharedCellsOnlyEqualKeys, duplicateKeysShareCell, at initial entry. The representation must identify PCM/RSL SDK cells and lamport-cell mappings with those admitted cells. NLF acquire/release tokens are threaded through the same current state, never reset from admission after a child or CPI. Rc count/drop, handle stability and CPI borrow-counter frames are not assumed.

Env is exactly RSL.Env revision 3. Env.reservation is bound to the existing headline reservation binder through EnvRep; no second fallible-reservation channel is introduced. Box/Vec/format allocation failures and named Rc-overflow clone aborts keep only ordered prefixes, with no post-abort state. Runtime replies and native callback graphs remain explicit slots.

No error-path log or return-data abstraction is adopted. Full ProgramError includes String payloads; the deposit/leaf helpers use their full native enums. Pool bodies move errors rather than clone them; the shared RSL owned-getter String clone arms remain in RSL revision 2/3. Every child graph must keep complete Results and exact log/return-data events.

RuntimeCpiAccountView, RuntimeReturnData and RuntimeReturnDataClear are named retained runtime items only. Passed cells are unconstrained across CPI. RuntimeCpiReadonlyEntry7 is PENDING/UNUSED. Return-register producer/context identity is a physical callback/representation obligation, never inferred from the arbitrary program_id argument.

| Pool row | Frozen function / lines | Module | Focused rejection check |
|---|---|---|---|
| POOL:328 | process_pair_forest_deposit_with_runtime_v1 [988, 1196] | PCM_Spec_POOL_328.lean | PCM_L080 exit 0 |
| POOL:330 | process_pair_forest_terminal_with_verifier_v1 [1615, 1821] | PCM_Spec_POOL_330.lean | PCM_L149 exit 0 |
| POOL:327 | process_pair_forest_checkpoint_with_runtime_v1 [2130, 2188] | PCM_Spec_POOL_327.lean | PCM_L082 exit 0 |
| POOL:350 | plan_pair_forest_terminal_dispatch_with_bytes_v1 [177, 249] | PCM_Spec_POOL_350.lean | PCM_L137 exit 0 |
| POOL:347 | dispatch_pair_forest_terminal_readonly_v1 [385, 423] | PCM_Spec_POOL_347.lean | PCM_L109 exit 0 |
| POOL:348 | invoke_pair_forest_terminal_with_runtime_v1 [281, 382] | PCM_Spec_POOL_348.lean | PCM_L110 exit 0 |
| POOL:311 | decode_terminal_checkpoint_box_v1 [1434, 1444] | PCM_Spec_POOL_311.lean | PCM_L099 exit 0 |
| POOL:312 | decode_terminal_lane_box_v1 [1447, 1470] | PCM_Spec_POOL_312.lean | PCM_L100 exit 0 |
| POOL:313 | decode_terminal_master_box_v1 [1422, 1431] | PCM_Spec_POOL_313.lean | PCM_L101 exit 0 |
| POOL:314 | decode_terminal_request_box_v1 [1412, 1419] | PCM_Spec_POOL_314.lean | PCM_L103 exit 0 |
| POOL:339 | validate_authenticated_terminal_result_v1 [1527, 1558] | PCM_Spec_POOL_339.lean | PCM_L128 exit 0 |
| POOL:319 | next_lane_image_box_v1 [1589, 1602] | PCM_Spec_POOL_319.lean | PCM_L104 exit 0 |
| POOL:320 | next_pair_forest_lane_v1 [1384, 1409] | PCM_Spec_POOL_320.lean | PCM_L001 exit 0 |
| POOL:165 | pool_v1_note_commitment [225, 232] | PCM_Spec_POOL_165.lean | PCM_L122 exit 0 |
| POOL:220 | leaf_digest [164, 170] | PCM_Spec_POOL_220.lean | PCM_L088 exit 0 |
| POOL:279 | append_roots_unchecked [273, 282] | PCM_Spec_POOL_279.lean | PCM_L144 exit 0 |
| POOL:286 | write_new_page_unchecked [247, 271] | PCM_Spec_POOL_286.lean | PCM_L145 exit 0 |
| POOL:289 | encoded_marker [232, 234] | PCM_Spec_POOL_289.lean | PCM_L089 exit 0 |
| POOL:294 | plan_pair_forest_nullifier_marker_consumption_v1 [244, 266] | PCM_Spec_POOL_294.lean | PCM_L114 exit 0 |
| POOL:301 | account_is_zeroed_program_page [806, 815] | PCM_Spec_POOL_301.lean | PCM_L141 exit 0 |
| POOL:304 | decode_deposit_lane_box_v1 [954, 977] | PCM_Spec_POOL_304.lean | PCM_L102 exit 0 |
| POOL:308 | decode_pair_forest_checkpoint_instruction_v1 [272, 277] | PCM_Spec_POOL_308.lean | PCM_L092 exit 0 |
| POOL:309 | decode_pair_forest_deposit_instruction_v1 [287, 291] | PCM_Spec_POOL_309.lean | PCM_L044 exit 0 |
| POOL:321 | plan_pair_forest_checkpoint_accounts_v1 [744, 788] | PCM_Spec_POOL_321.lean | PCM_L129 exit 0 |
| POOL:322 | plan_pair_forest_spend_layout_v1 [1218, 1319] | PCM_Spec_POOL_322.lean | PCM_L130 exit 0 |
| POOL:326 | prepare_deposit_append_v1 [919, 951] | PCM_Spec_POOL_326.lean | PCM_L107 exit 0 |
| POOL:333 | require_program_owned_zeroed [400, 415] | PCM_Spec_POOL_333.lean | PCM_L135 exit 0 |
| POOL:334 | split_pair_forest_terminal_bump_hints_v1 [139, 156] | PCM_Spec_POOL_334.lean | PCM_L093 exit 0 |
| POOL:336 | terminal_common_box_v1 [1473, 1502] | PCM_Spec_POOL_336.lean | PCM_L124 exit 0 |
| POOL:337 | terminal_result_bytes_box_v1 [1605, 1612] | PCM_Spec_POOL_337.lean | PCM_L108 exit 0 |
| POOL:338 | transfer_terminal_statement_box_v1 [1505, 1513] | PCM_Spec_POOL_338.lean | PCM_L125 exit 0 |
| POOL:340 | validate_lane_current_page [817, 860] | PCM_Spec_POOL_340.lean | PCM_L136 exit 0 |
| POOL:341 | validate_pair_forest_request_accounts_v1 [1321, 1382] | PCM_Spec_POOL_341.lean | PCM_L138 exit 0 |
| POOL:342 | withdrawal_terminal_statement_box_v1 [1516, 1524] | PCM_Spec_POOL_342.lean | PCM_L126 exit 0 |
| POOL:349 | plan_pair_forest_terminal_dispatch_v1 [144, 174] | PCM_Spec_POOL_349.lean | PCM_L139 exit 0 |
| POOL:356 | invoke [83, 89] | PCM_Spec_POOL_356.lean | PCM_L112 exit 0 |
| POOL:357 | invoke_signed [91, 98] | PCM_Spec_POOL_357.lean | PCM_L113 exit 0 |
| POOL:358 | create_or_allocate_pda [182, 202] | PCM_Spec_POOL_358.lean | PCM_L111 exit 0 |
| POOL:361 | create_pair_forest_nullifier_marker_if_needed_v1 [450, 485] | PCM_Spec_POOL_361.lean | PCM_L148 exit 0 |
| POOL:362 | plan_fresh_program_pda [156, 180] | PCM_Spec_POOL_362.lean | PCM_L140 exit 0 |
| POOL:367 | require_unique_accounts [123, 132] | PCM_Spec_POOL_367.lean | PCM_L094 exit 0 |
| POOL:382 | exact_transfer_account_infos_v1 [339, 350] | PCM_Spec_POOL_382.lean | PCM_L115 exit 0 |
| POOL:383 | exact_withdrawal_transfer_account_infos_v1 [535, 547] | PCM_Spec_POOL_383.lean | PCM_L116 exit 0 |
| POOL:388 | plan_legacy_deposit_transfer_from_identity_v1 [234, 337] | PCM_Spec_POOL_388.lean | PCM_L131 exit 0 |
| POOL:389 | plan_legacy_withdrawal_transfer_from_identity_v1 [387, 533] | PCM_Spec_POOL_389.lean | PCM_L132 exit 0 |
| POOL:395 | validate_exact_deposit_delta_v1 [586, 617] | PCM_Spec_POOL_395.lean | PCM_L133 exit 0 |
| POOL:396 | validate_exact_withdrawal_delta_v1 [551, 582] | PCM_Spec_POOL_396.lean | PCM_L134 exit 0 |

The rejection examples for wrappers that first call an OPEN child explicitly require that child's canonical graph at a real rejecting argument (never a successful endpoint). They are not parent roots and are not claims that an uninstalled graph is CLOSED. The source-to-graph, domain and representation installations remain stage-2/3 obligations.

P4 is the complete 330 continuation after verifier return, including three exclusive guards, optional withdrawal invoke/delta check, ordered lane/page/marker writes, the SAME return-data callback and reverse guard release. The guard-free fixed helpers 336/338/342 are transcribed explicitly, preserving both Box abort sites before validation in 339.

Real direct calls are taken from the frozen source. Conservative MIR alternatives to new/from/get/invoke are not silently adopted as direct calls or excluded from any Pool ledger row. No inventory row is promoted or re-owned.

Freeze covers all own semantic dependency sources below, not just the per-function filenames. Subsequent changes require a demonstrated error against the frozen source, shown by the finder and applied by the Stream C lead (bp)(4). Remaining interfaces may be instantiated without editing this frozen set.

Target not yet established.
