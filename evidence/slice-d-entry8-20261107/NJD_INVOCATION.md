# NJD invocation inventory

All 17 rows remain OPEN. Calls are ordered by expression completion (arguments before their enclosing call), with conditional/loop guards retained in the pinned source; this is not an unconditional flat trace. Frozen call arguments below are verbatim source expressions; the emitted canonical body inspection is NJD_INSPECT.txt. NIV_L022 supplies entry/process emission; owned bodies use canonical AdapterRwModel. Slot correction: digest/error are op43/op44; decoders master/checkpoint/lane are op48/op49/op50. SDK stages are wrappers, not declarations AdapterRw.r1_pool_adapter.owned.stage1/stage2.

A CLOSED row listed here identifies the law source, not a discharge. Each caller must instantiate its complete Result, same arguments and full frame under (aq). Unmatched primitive/SDK calls are exact missing-law entries, not P7 assumptions. Runtime entry admission supplies only its seven fields and does not prove SDK implementation laws. No candidate child success or RuntimeCpiReadonlyEntry7 is used.

## TX1:330 process_r1_cost_probe_instruction

1. L57 `cfg(feature="pool-adapter")`: MISSING exact specialization/packet/frame lemma; cannot assume
2. L61 `pool_route::admitted(data)`: CLOSED row (domain and full packet still to instantiate) [TX1:331, TX2:214]
3. L64 `r1_pool_adapter::process(program_id,accounts,data)`: MISSING CLOSED callee packet [TX1:333, TX2:221]

Canonical call dependencies: `programs/r1-cost-probe/src/pool_route.rs::admitted`, `programs/r1-cost-probe/src/r1_pool_adapter.rs::process`.

## TX1:333 process

1. L955 `first()`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
2. L955 `copied()`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
3. L956 `lifecycle_init(program_id, accounts, data)`: MISSING exact specialization/packet/frame lemma; cannot assume
4. L957 `lifecycle_write(program_id, accounts, data)`: MISSING exact specialization/packet/frame lemma; cannot assume
5. L958 `lifecycle_finalize(program_id, accounts, data)`: MISSING exact specialization/packet/frame lemma; cannot assume
6. L959 `stage1(program_id, accounts, data)`: MISSING CLOSED callee packet [TX1:344]
7. L960 `stage2(program_id, accounts, data)`: MISSING CLOSED callee packet [TX2:240]

Canonical call dependencies: `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage1`, `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage2`.

## TX1:344 stage1

1. L448 `len()`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
2. L452 `snapshot(&accounts[0], POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES + verifier::PROOF_BYTES, POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES + verifier::PROOF_BYTES)`: CLOSED row (domain and full packet still to instantiate) [TX1:343, TX2:239]
3. L453 `snapshot(&accounts[1], POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES, POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES)`: CLOSED row (domain and full packet still to instantiate) [TX1:343, TX2:239]
4. L454 `snapshot(&accounts[2], CHECKPOINT_TAIL_BYTES, CHECKPOINT_TAIL_BYTES)`: CLOSED row (domain and full packet still to instantiate) [TX1:343, TX2:239]
5. L456 `stage1_owned(program_id, &owned, data)`: MISSING CLOSED callee packet [TX1:345]
6. L457 `try_borrow_mut_data()`: SDK borrow law requires pinned P7/retained S2TrustedSdkBorrow matching; RuntimeEntrypointAdmission alone insufficient
7. L457 `copy_from_slice(&checkpoint)`: MISSING exact specialization/packet/frame lemma; cannot assume
8. L458 `cfg(feature="cu-profiling")`: MISSING exact specialization/packet/frame lemma; cannot assume
9. L459 `solana_program::log::sol_log_compute_units()`: MISSING exact specialization/packet/frame lemma; cannot assume

Canonical call dependencies: `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::snapshot`, `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage1_owned`.

## TX1:345 stage1_owned

1. L377 `len()`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
2. L383 `require_distinct_accounts(&[proof_account, public_account, checkpoint_account])`: CLOSED row (domain and full packet still to instantiate) [TX1:339, TX2:235]
3. L384 `require_readonly_buffer(proof_account)`: CLOSED row (domain and full packet still to instantiate) [TX1:340, TX2:237]
4. L385 `require_readonly_buffer(public_account)`: CLOSED row (domain and full packet still to instantiate) [TX1:340, TX2:237]
5. L386 `require_verifier_checkpoint(checkpoint_account, program_id, true)`: CLOSED row (domain and full packet still to instantiate) [TX1:341, TX2:238]
6. L387 `data()`: CLOSED row (domain and full packet still to instantiate) [TX1:335, TX2:229]
7. L388 `require_zero(checkpoint_data)`: CLOSED row (domain and full packet still to instantiate) [TX1:342]
8. L389 `data()`: CLOSED row (domain and full packet still to instantiate) [TX1:335, TX2:229]
9. L390 `decode_public_statement_box(&public_data)`: CLOSED row (domain and full packet still to instantiate) [TX1:332]
10. L391 `validate_pool_v1_pair_forest_terminal_statement_v1(&statement)`: CLOSED row (domain and full packet still to instantiate) [TX1:276, TX2:169]
11. L392 `map_err(|_| ProgramError::InvalidAccountData)`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
12. L394 `common()`: CLOSED row (domain and full packet still to instantiate) [TX1:267, TX2:160]
13. L393 `encode_pool_v1_pair_verified_afterstate_v1(&statement.common().lane_transition.candidate_afterstate,)`: CLOSED row (domain and full packet still to instantiate) [TX1:278, TX2:172]
14. L396 `map_err(|_| ProgramError::InvalidAccountData)`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
15. L398 `data()`: CLOSED row (domain and full packet still to instantiate) [TX1:335, TX2:229]
16. L401 `checked_add(proof_length)`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
17. L402 `ok_or(ProgramError::InvalidAccountData)`: MISSING exact specialization/packet/frame lemma; cannot assume
18. L403 `len()`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
19. L405 `tag()`: CLOSED row (domain and full packet still to instantiate) [TX1:173, TX2:098]
20. L409 `semantic_public()`: MISSING CLOSED callee packet [TX1:268]
21. L409 `super::super::first_decoded(statement.semantic_public(), &public_data, &proof_data[proof_start..proof_end], data[1] as usize)`: MISSING CLOSED callee packet [TX1:328]
22. L410 `len()`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
23. L410 `len()`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name

Canonical call dependencies: `crates/aspis-r1-cost-probe/src/transport.rs::Variant::tag`, `crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalStatementV1::common`, `crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalStatementV1::semantic_public`, `crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::validate_pool_v1_pair_forest_terminal_statement_v1`, `crates/aspis-statement/src/pool_v1/pair_terminal.rs::encode_pool_v1_pair_verified_afterstate_v1`, `programs/r1-cost-probe/src/lib.rs::first_decoded`, `programs/r1-cost-probe/src/r1_pool_adapter.rs::decode_public_statement_box`, `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::data`, `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_distinct_accounts`, `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_readonly_buffer`, `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_verifier_checkpoint`, `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_zero`.

## TX1:328 first_decoded

1. L50 `observer()`: MISSING CLOSED callee packet [TX1:329, TX2:212]
2. L50 `verifier::tx1(public,public_bytes,proof,k,SolanaDigest,observer())`: MISSING CLOSED callee packet [TX1:094]
3. L50 `map_err(error)`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name

Canonical call dependencies: `crates/aspis-r1-cost-probe/src/candidate.rs::tx1`, `programs/r1-cost-probe/src/lib.rs::error`, `programs/r1-cost-probe/src/lib.rs::observer`.

## TX2:213 process_r1_cost_probe_instruction

1. L57 `cfg(feature="pool-adapter")`: MISSING exact specialization/packet/frame lemma; cannot assume
2. L61 `pool_route::admitted(data)`: CLOSED row (domain and full packet still to instantiate) [TX1:331, TX2:214]
3. L64 `r1_pool_adapter::process(program_id,accounts,data)`: MISSING CLOSED callee packet [TX1:333, TX2:221]

Canonical call dependencies: `programs/r1-cost-probe/src/pool_route.rs::admitted`, `programs/r1-cost-probe/src/r1_pool_adapter.rs::process`.

## TX2:221 process

1. L955 `first()`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
2. L955 `copied()`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
3. L956 `lifecycle_init(program_id, accounts, data)`: MISSING exact specialization/packet/frame lemma; cannot assume
4. L957 `lifecycle_write(program_id, accounts, data)`: MISSING exact specialization/packet/frame lemma; cannot assume
5. L958 `lifecycle_finalize(program_id, accounts, data)`: MISSING exact specialization/packet/frame lemma; cannot assume
6. L959 `stage1(program_id, accounts, data)`: MISSING CLOSED callee packet [TX1:344]
7. L960 `stage2(program_id, accounts, data)`: MISSING CLOSED callee packet [TX2:240]

Canonical call dependencies: `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage1`, `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage2`.

## TX2:240 stage2

1. L464 `len()`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
2. L464 `get(..4)`: CLOSED row (domain and full packet still to instantiate) [TX1:062, TX2:043]
3. L467 `program::set_return_data(&[])`: RuntimeReturnDataClear for empty argument; native exact slice/effects cut remains OPEN
4. L468 `cfg(feature="cu-profiling")`: MISSING exact specialization/packet/frame lemma; cannot assume
5. L469 `solana_program::log::sol_log_compute_units()`: MISSING exact specialization/packet/frame lemma; cannot assume
6. L471 `snapshot(&accounts[0], POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES + verifier::PROOF_BYTES, POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES + verifier::PROOF_BYTES)`: CLOSED row (domain and full packet still to instantiate) [TX1:343, TX2:239]
7. L472 `snapshot(&accounts[1], POOL_V1_PAIR_FOREST_MASTER_ACCOUNT_BYTES, POOL_V1_PAIR_FOREST_MASTER_ACCOUNT_BYTES)`: CLOSED row (domain and full packet still to instantiate) [TX1:343, TX2:239]
8. L473 `snapshot(&accounts[2], POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES, POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES)`: CLOSED row (domain and full packet still to instantiate) [TX1:343, TX2:239]
9. L474 `snapshot(&accounts[3], POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES, POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES)`: CLOSED row (domain and full packet still to instantiate) [TX1:343, TX2:239]
10. L475 `snapshot(&accounts[4], POOL_V1_VERIFIER_REGISTRY_BYTES, POOL_V1_VERIFIER_REGISTRY_V2_BYTES)`: CLOSED row (domain and full packet still to instantiate) [TX1:343, TX2:239]
11. L476 `snapshot(&accounts[5], POOL_V1_VERIFIER_ENTRY_BYTES, POOL_V1_VERIFIER_ENTRY_V2_BYTES)`: CLOSED row (domain and full packet still to instantiate) [TX1:343, TX2:239]
12. L477 `snapshot(&accounts[6], CHECKPOINT_TAIL_BYTES, CHECKPOINT_TAIL_BYTES)`: CLOSED row (domain and full packet still to instantiate) [TX1:343, TX2:239]
13. L479 `Clock::get()`: CLOSED row (domain and full packet still to instantiate) [TX1:062, TX2:043]
14. L480 `stage2_owned(program_id, &owned, data, current_slot)`: MISSING CLOSED callee packet [TX2:241]

Canonical call dependencies: `crates/aspis-core/src/r0/domain.rs::FibreIndex::get`, `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::snapshot`, `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage2_owned`.

## TX2:241 stage2_owned

1. L418 `len()`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
2. L418 `get(..4)`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
3. L422 `validate_asq8(program_id, accounts, data, current_slot)`: MISSING CLOSED callee packet [TX2:242]
4. L423 `data()`: CLOSED row (domain and full packet still to instantiate) [TX1:335, TX2:229]
5. L424 `data()`: CLOSED row (domain and full packet still to instantiate) [TX1:335, TX2:229]
6. L426 `checked_add(validated.proof_length)`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
7. L427 `ok_or(ProgramError::InvalidAccountData)`: MISSING exact specialization/packet/frame lemma; cannot assume
8. L428 `len()`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
9. L431 `encode_pool_v1_pair_forest_terminal_statement_v1(&validated.statement)`: CLOSED row (domain and full packet still to instantiate) [TX2:165]
10. L432 `map_err(|_| ProgramError::InvalidInstructionData)`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
11. L433 `len()`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
12. L441 `super::super::observer()`: MISSING CLOSED callee packet [TX1:329, TX2:212]
13. L436 `verifier::tx2_authenticated(&public_bytes, &proof_data[proof_start..proof_end], &checkpoint_data, super::super::SolanaDigest, super::super::observer(),)`: MISSING CLOSED callee packet [TX2:064]
14. L443 `map_err(super::super::error)`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
15. L444 `emit_result(&validated.statement)`: CLOSED row (domain and full packet still to instantiate) [TX2:219]

Canonical call dependencies: `crates/aspis-r1-cost-probe/src/candidate.rs::tx2_authenticated`, `crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::encode_pool_v1_pair_forest_terminal_statement_v1`, `programs/r1-cost-probe/src/lib.rs::error`, `programs/r1-cost-probe/src/lib.rs::observer`, `programs/r1-cost-probe/src/r1_pool_adapter.rs::emit_result`, `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::data`, `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::validate_asq8`.

## TX2:216 decode_checkpoint_box

1. L439 `decode_pool_v1_pair_forest_checkpoint_v1(bytes)`: MISSING CLOSED callee packet [TX2:152]
2. L440 `map_err(|_| ProgramError::InvalidAccountData)`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
3. L438 `Box::new(decode_pool_v1_pair_forest_checkpoint_v1(bytes) .map_err(|_| ProgramError::InvalidAccountData)?,)`: MISSING exact specialization/packet/frame lemma; cannot assume

Canonical call dependencies: `crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::decode_pool_v1_pair_forest_checkpoint_v1`.

## TX2:217 decode_lane_from_pool_release

1. L452 `len()`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
2. L455 `usize::from(bytes[5])`: MISSING exact specialization/packet/frame lemma; cannot assume
3. L460 `iter()`: MISSING exact specialization/packet/frame lemma; cannot assume
4. L461 `any(|byte| *byte != 0)`: MISSING exact specialization/packet/frame lemma; cannot assume
5. L466 `try_into()`: MISSING exact specialization/packet/frame lemma; cannot assume
6. L467 `map_err(|_| ProgramError::InvalidAccountData)`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
7. L482 `try_into()`: MISSING exact specialization/packet/frame lemma; cannot assume
8. L483 `map_err(|_| ProgramError::InvalidAccountData)`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
9. L480 `u64::from_le_bytes(tree[8..16] .try_into() .map_err(|_| ProgramError::InvalidAccountData)?,)`: MISSING exact specialization/packet/frame lemma; cannot assume
10. L490 `try_into()`: MISSING exact specialization/packet/frame lemma; cannot assume
11. L491 `map_err(|_| ProgramError::InvalidAccountData)`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
12. L488 `decode_digest_canonical(tree[16..48] .try_into() .map_err(|_| ProgramError::InvalidAccountData)?,)`: CLOSED row (domain and full packet still to instantiate) [TX1:198, TX2:146]
13. L493 `map_err(|_| ProgramError::InvalidAccountData)`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
14. L495 `iter_mut()`: MISSING exact specialization/packet/frame lemma; cannot assume
15. L495 `enumerate()`: MISSING exact specialization/packet/frame lemma; cannot assume
16. L499 `try_into()`: MISSING exact specialization/packet/frame lemma; cannot assume
17. L500 `map_err(|_| ProgramError::InvalidAccountData)`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
18. L497 `decode_digest_canonical(tree[start..start + 32] .try_into() .map_err(|_| ProgramError::InvalidAccountData)?,)`: CLOSED row (domain and full packet still to instantiate) [TX1:198, TX2:146]
19. L502 `map_err(|_| ProgramError::InvalidAccountData)`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
20. L510 `Box::new(PoolV1PairForestLaneStateV1 { bump: bytes[72], master, lane_id: bytes[5], tree: IncrementalMerkleTreeV1 { next_leaf_index, root, frontier, }, })`: MISSING exact specialization/packet/frame lemma; cannot assume

Canonical call dependencies: `crates/aspis-statement/src/atomic_statement.rs::decode_digest_canonical`.

## TX2:218 decode_master_box

1. L431 `decode_pool_v1_pair_forest_master_v1(bytes)`: MISSING CLOSED callee packet [TX2:153]
2. L432 `map_err(|_| ProgramError::InvalidAccountData)`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
3. L430 `Box::new(decode_pool_v1_pair_forest_master_v1(bytes) .map_err(|_| ProgramError::InvalidAccountData)?,)`: MISSING exact specialization/packet/frame lemma; cannot assume

Canonical call dependencies: `crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::decode_pool_v1_pair_forest_master_v1`.

## TX2:233 authenticate_asq8_accounts

1. L240 `len()`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
2. L246 `require_readonly_buffer(proof_account)`: CLOSED row (domain and full packet still to instantiate) [TX1:340, TX2:237]
3. L247 `require_verifier_checkpoint(verifier_checkpoint, verifier_program, false)`: CLOSED row (domain and full packet still to instantiate) [TX1:341, TX2:238]
4. L248 `require_readonly_account(master_account, pool_program)`: CLOSED row (domain and full packet still to instantiate) [TX2:236]
5. L249 `require_readonly_account(checkpoint_account, pool_program)`: CLOSED row (domain and full packet still to instantiate) [TX2:236]
6. L250 `require_readonly_account(lane_account, pool_program)`: CLOSED row (domain and full packet still to instantiate) [TX2:236]
7. L251 `require_distinct_accounts(&[ proof_account, master_account, checkpoint_account, lane_account, registry_account, entry_account, verifier_checkpoint, ])`: CLOSED row (domain and full packet still to instantiate) [TX1:339, TX2:235]
8. L261 `data()`: CLOSED row (domain and full packet still to instantiate) [TX1:335, TX2:229]
9. L261 `decode_master_box(master_account.data()?)`: MISSING CLOSED callee packet [TX2:218]
10. L262 `key()`: CLOSED row (domain and full packet still to instantiate) [TX1:337, TX2:231]
11. L262 `to_bytes()`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
12. L267 `Pubkey::new_from_array(master.identity.asset_mint)`: MISSING exact specialization/packet/frame lemma; cannot assume
13. L267 `as_ref()`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
14. L264 `Pubkey::create_program_address(&[ PAIR_FOREST_MASTER_SEED, Pubkey::new_from_array(master.identity.asset_mint).as_ref(), &[master.bump], ], pool_program,)`: MISSING exact specialization/packet/frame lemma; cannot assume
15. L272 `map_err(|_| ProgramError::InvalidAccountData)`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
16. L272 `key()`: CLOSED row (domain and full packet still to instantiate) [TX1:337, TX2:231]
17. L276 `authenticate_invariant_release_registry(verifier_program, pool_program, master_account, &master, registry_account, entry_account, current_slot,)`: MISSING CLOSED callee packet [TX2:234]
18. L286 `data()`: CLOSED row (domain and full packet still to instantiate) [TX1:335, TX2:229]
19. L286 `decode_checkpoint_box(checkpoint_account.data()?)`: MISSING CLOSED callee packet [TX2:216]
20. L287 `key()`: CLOSED row (domain and full packet still to instantiate) [TX1:337, TX2:231]
21. L287 `to_bytes()`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
22. L292 `key()`: CLOSED row (domain and full packet still to instantiate) [TX1:337, TX2:231]
23. L292 `as_ref()`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
24. L293 `to_le_bytes()`: CLOSED row (domain and full packet still to instantiate) [TX1:022, TX1:058, TX2:016, TX2:039]
25. L289 `Pubkey::create_program_address(&[ PAIR_FOREST_CHECKPOINT_SEED, master_account.key().as_ref(), &checkpoint.checkpoint_sequence.to_le_bytes(), &[checkpoint.bump], ], pool_program,)`: MISSING exact specialization/packet/frame lemma; cannot assume
26. L298 `map_err(|_| ProgramError::InvalidAccountData)`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
27. L298 `key()`: CLOSED row (domain and full packet still to instantiate) [TX1:337, TX2:231]
28. L302 `data()`: CLOSED row (domain and full packet still to instantiate) [TX1:335, TX2:229]
29. L302 `decode_lane_from_pool_release(lane_account.data()?)`: MISSING CLOSED callee packet [TX2:217]
30. L303 `key()`: CLOSED row (domain and full packet still to instantiate) [TX1:337, TX2:231]
31. L303 `to_bytes()`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
32. L308 `key()`: CLOSED row (domain and full packet still to instantiate) [TX1:337, TX2:231]
33. L308 `as_ref()`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
34. L305 `Pubkey::create_program_address(&[ PAIR_FOREST_LANE_SEED, master_account.key().as_ref(), &[output_lane], &[selected_lane.bump], ], pool_program,)`: MISSING exact specialization/packet/frame lemma; cannot assume
35. L314 `map_err(|_| ProgramError::InvalidAccountData)`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
36. L314 `key()`: CLOSED row (domain and full packet still to instantiate) [TX1:337, TX2:231]
37. L319 `key()`: CLOSED row (domain and full packet still to instantiate) [TX1:337, TX2:231]
38. L319 `to_bytes()`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
39. L318 `Box::new(PoolV1PairLiveSnapshotV1 { pool: master_account.key().to_bytes(), deployment_domain: master.identity.deployment_domain, sequence: selected_lane.tree.next_leaf_index, next_pair_index: selected_lane.tree.next_leaf_index, current_root: selected_lane.tree.root, frontier: selected_lane.tree.frontier, })`: MISSING exact specialization/packet/frame lemma; cannot assume
40. L327 `key()`: CLOSED row (domain and full packet still to instantiate) [TX1:337, TX2:231]
41. L327 `to_bytes()`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
42. L328 `key()`: CLOSED row (domain and full packet still to instantiate) [TX1:337, TX2:231]
43. L328 `to_bytes()`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
44. L329 `key()`: CLOSED row (domain and full packet still to instantiate) [TX1:337, TX2:231]
45. L329 `to_bytes()`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name

Canonical call dependencies: `crates/aspis-core/src/field.rs::M31::to_le_bytes`, `crates/aspis-core/src/field/wide_exact.rs::WideExact::to_le_bytes`, `programs/r1-cost-probe/src/r1_pool_adapter.rs::decode_checkpoint_box`, `programs/r1-cost-probe/src/r1_pool_adapter.rs::decode_lane_from_pool_release`, `programs/r1-cost-probe/src/r1_pool_adapter.rs::decode_master_box`, `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::data`, `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::key`, `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::authenticate_invariant_release_registry`, `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_distinct_accounts`, `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_readonly_account`, `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_readonly_buffer`, `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_verifier_checkpoint`.

## TX2:234 authenticate_invariant_release_registry

1. L93 `to_bytes()`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
2. L93 `pool_program_id()`: CLOSED row (domain and full packet still to instantiate) [TX2:220]
3. L95 `registry_program_id()`: CLOSED row (domain and full packet still to instantiate) [TX2:225]
4. L101 `validate_verifier_policy_v1(&master.verifier_policy)`: CLOSED row (domain and full packet still to instantiate) [TX2:151]
5. L102 `map_err(|_| ProgramError::InvalidAccountData)`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
6. L103 `registry_program_id()`: CLOSED row (domain and full packet still to instantiate) [TX2:225]
7. L103 `Pubkey::new_from_array(registry_program_id())`: MISSING exact specialization/packet/frame lemma; cannot assume
8. L104 `require_readonly_account(registry_account, &registry_program)`: CLOSED row (domain and full packet still to instantiate) [TX2:236]
9. L108 `bpf_loader_upgradeable::id()`: MISSING exact specialization/packet/frame lemma; cannot assume
10. L109 `data()`: CLOSED row (domain and full packet still to instantiate) [TX1:335, TX2:229]
11. L109 `decode_verifier_registry_v2(registry_account.data()?)`: CLOSED row (domain and full packet still to instantiate) [TX2:204]
12. L110 `map_err(|_| ProgramError::InvalidAccountData)`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
13. L114 `key()`: CLOSED row (domain and full packet still to instantiate) [TX1:337, TX2:231]
14. L114 `as_ref()`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
15. L111 `Pubkey::create_program_address(&[ VERIFIER_REGISTRY_V2_SEED, master_account.key().as_ref(), &[registry.bump], ], &registry_program,)`: MISSING exact specialization/packet/frame lemma; cannot assume
16. L119 `map_err(|_| ProgramError::InvalidAccountData)`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
17. L120 `key()`: CLOSED row (domain and full packet still to instantiate) [TX1:337, TX2:231]
18. L124 `as_ref()`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
19. L123 `Pubkey::create_program_address(&[registry_program.as_ref(), &[registry.programdata_bump]], &loader,)`: MISSING exact specialization/packet/frame lemma; cannot assume
20. L127 `map_err(|_| ProgramError::InvalidAccountData)`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
21. L128 `key()`: CLOSED row (domain and full packet still to instantiate) [TX1:337, TX2:231]
22. L128 `to_bytes()`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
23. L131 `to_bytes()`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
24. L132 `to_bytes()`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
25. L133 `to_bytes()`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
26. L134 `is_immutable()`: CLOSED row (domain and full packet still to instantiate) [TX2:197, TX2:199]
27. L135 `is_paused()`: CLOSED row (domain and full packet still to instantiate) [TX2:198, TX2:200]
28. L139 `require_readonly_account(entry_account, &registry_program)`: CLOSED row (domain and full packet still to instantiate) [TX2:236]
29. L140 `data()`: CLOSED row (domain and full packet still to instantiate) [TX1:335, TX2:229]
30. L140 `decode_verifier_registry_entry_v2(entry_account.data()?)`: CLOSED row (domain and full packet still to instantiate) [TX2:202]
31. L141 `map_err(|_| ProgramError::InvalidAccountData)`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
32. L145 `key()`: CLOSED row (domain and full packet still to instantiate) [TX1:337, TX2:231]
33. L145 `as_ref()`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
34. L142 `Pubkey::create_program_address(&[ VERIFIER_ENTRY_V2_SEED, master_account.key().as_ref(), &PROFILE_BINDING, &RELEASE_BINDING, &[entry.bump], ], &registry_program,)`: MISSING exact specialization/packet/frame lemma; cannot assume
35. L152 `map_err(|_| ProgramError::InvalidAccountData)`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
36. L153 `key()`: CLOSED row (domain and full packet still to instantiate) [TX1:337, TX2:231]
37. L157 `as_ref()`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
38. L156 `Pubkey::create_program_address(&[verifier_program.as_ref(), &[entry.programdata_bump]], &loader,)`: MISSING exact specialization/packet/frame lemma; cannot assume
39. L160 `map_err(|_| ProgramError::InvalidAccountData)`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
40. L161 `key()`: CLOSED row (domain and full packet still to instantiate) [TX1:337, TX2:231]
41. L161 `to_bytes()`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
42. L163 `to_bytes()`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
43. L167 `to_bytes()`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
44. L168 `to_bytes()`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
45. L170 `is_active_at(current_slot)`: CLOSED row (domain and full packet still to instantiate) [TX2:194, TX2:196]
46. L177 `data()`: CLOSED row (domain and full packet still to instantiate) [TX1:335, TX2:229]
47. L177 `decode_verifier_registry_v1(registry_account.data()?)`: MISSING CLOSED callee packet [TX2:203]
48. L178 `map_err(|_| ProgramError::InvalidAccountData)`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
49. L182 `key()`: CLOSED row (domain and full packet still to instantiate) [TX1:337, TX2:231]
50. L182 `as_ref()`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
51. L179 `Pubkey::create_program_address(&[ VERIFIER_REGISTRY_SEED, master_account.key().as_ref(), &[registry.bump], ], &registry_program,)`: MISSING exact specialization/packet/frame lemma; cannot assume
52. L187 `map_err(|_| ProgramError::InvalidAccountData)`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
53. L188 `key()`: CLOSED row (domain and full packet still to instantiate) [TX1:337, TX2:231]
54. L191 `key()`: CLOSED row (domain and full packet still to instantiate) [TX1:337, TX2:231]
55. L191 `to_bytes()`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
56. L194 `is_immutable()`: CLOSED row (domain and full packet still to instantiate) [TX2:197, TX2:199]
57. L195 `is_paused()`: CLOSED row (domain and full packet still to instantiate) [TX2:198, TX2:200]
58. L199 `require_readonly_account(entry_account, &registry_program)`: CLOSED row (domain and full packet still to instantiate) [TX2:236]
59. L200 `data()`: CLOSED row (domain and full packet still to instantiate) [TX1:335, TX2:229]
60. L200 `decode_verifier_registry_entry_v1(entry_account.data()?)`: MISSING CLOSED callee packet [TX2:201]
61. L201 `map_err(|_| ProgramError::InvalidAccountData)`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
62. L205 `key()`: CLOSED row (domain and full packet still to instantiate) [TX1:337, TX2:231]
63. L205 `as_ref()`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
64. L202 `Pubkey::create_program_address(&[ VERIFIER_ENTRY_SEED, master_account.key().as_ref(), &PROFILE_BINDING, &RELEASE_BINDING, &[entry.bump], ], &registry_program,)`: MISSING exact specialization/packet/frame lemma; cannot assume
65. L212 `map_err(|_| ProgramError::InvalidAccountData)`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
66. L213 `key()`: CLOSED row (domain and full packet still to instantiate) [TX1:337, TX2:231]
67. L216 `key()`: CLOSED row (domain and full packet still to instantiate) [TX1:337, TX2:231]
68. L216 `to_bytes()`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
69. L218 `to_bytes()`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
70. L222 `is_active_at(current_slot)`: CLOSED row (domain and full packet still to instantiate) [TX2:194, TX2:196]

Canonical call dependencies: `crates/aspis-statement/src/pool_v1/format.rs::validate_verifier_policy_v1`, `crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryEntryV1::is_active_at`, `crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryEntryV2::is_active_at`, `crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV1::is_immutable`, `crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV1::is_paused`, `crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV2::is_immutable`, `crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV2::is_paused`, `crates/aspis-statement/src/pool_v1/verifier_registry.rs::decode_verifier_registry_entry_v1`, `crates/aspis-statement/src/pool_v1/verifier_registry.rs::decode_verifier_registry_entry_v2`, `crates/aspis-statement/src/pool_v1/verifier_registry.rs::decode_verifier_registry_v1`, `crates/aspis-statement/src/pool_v1/verifier_registry.rs::decode_verifier_registry_v2`, `programs/r1-cost-probe/src/r1_pool_adapter.rs::pool_program_id`, `programs/r1-cost-probe/src/r1_pool_adapter.rs::registry_program_id`, `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::data`, `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::key`, `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_readonly_account`.

## TX2:242 validate_asq8

1. L344 `len()`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
2. L347 `decode_pool_v1_pair_forest_terminal_request_v1(instruction_data)`: CLOSED row (domain and full packet still to instantiate) [TX2:163]
3. L348 `map_err(|_| ProgramError::InvalidInstructionData)`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
4. L351 `pool_program_id()`: CLOSED row (domain and full packet still to instantiate) [TX2:220]
5. L355 `Pubkey::new_from_array(request.pool_program)`: MISSING exact specialization/packet/frame lemma; cannot assume
6. L356 `nullifier()`: CLOSED row (domain and full packet still to instantiate) [TX2:158, TX2:161]
7. L356 `pool_v1_pair_forest_output_lane_v1(request.public.nullifier())`: CLOSED row (domain and full packet still to instantiate) [TX1:207, TX2:156]
8. L357 `map_err(|_| ProgramError::InvalidInstructionData)`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
9. L358 `authenticate_asq8_accounts(verifier_program, accounts, &pool_program, output_lane, current_slot?,)`: MISSING CLOSED callee packet [TX2:233]
10. L365 `first()`: P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name
11. L365 `ok_or(ProgramError::NotEnoughAccountKeys)`: MISSING exact specialization/packet/frame lemma; cannot assume
12. L366 `data()`: CLOSED row (domain and full packet still to instantiate) [TX1:335, TX2:229]
13. L366 `scan_proof_buffer(proof_account.data()?)`: CLOSED row (domain and full packet still to instantiate) [TX2:226]
14. L368 `reconstruct_asq8_statement(&request, &authenticated, &scanned.candidate_afterstate)`: CLOSED row (domain and full packet still to instantiate) [TX2:224]

Canonical call dependencies: `crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::pool_v1_pair_forest_output_lane_v1`, `crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalPaymentV1::nullifier`, `crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalStatementV1::nullifier`, `crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::decode_pool_v1_pair_forest_terminal_request_v1`, `programs/r1-cost-probe/src/r1_pool_adapter.rs::pool_program_id`, `programs/r1-cost-probe/src/r1_pool_adapter.rs::reconstruct_asq8_statement`, `programs/r1-cost-probe/src/r1_pool_adapter.rs::scan_proof_buffer`, `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::data`, `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::authenticate_asq8_accounts`.

## TX1:329 observer


Canonical call dependencies: .

## TX2:212 observer


Canonical call dependencies: .

