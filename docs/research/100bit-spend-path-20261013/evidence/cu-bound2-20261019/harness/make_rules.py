#!/usr/bin/env python3
"""Code-cited exclusions, loop trip caps and callee caps for residual.py (second CU bound).
Every entry names the source that makes it hold; citations are to research cf1828114 unless a
crate version is named (Cargo.lock pins solana-program-entrypoint 2.3.0, solana-instruction
2.3.3, bincode 1.3.3, solana-program 2.3.0, solana-pubkey as locked).
usage: make_rules.py out.json"""
import json, sys
ABORT = ('panicking|panic_bounds_check|index_len_fail|index_order_fail|unwrap_failed|handle_alloc_error|'
         'raw_vec12handle_error|assert_failed|len_mismatch_fail|panic_already|expect_failed|panic_fmt|custom_panic|'
         'capacity_overflow|slice_start_index|slice_end_index|str_index_overflow|overflow_fail|5abort')
X = []
def ex(id_, reason, citation, **m): X.append(dict(id=id_, reason=reason, citation=citation, **m))

# --- positional Vec growth: the pushed lengths are fixed, so the capacity test is decided by layout
ex('X-VEC-CHECKPOINT', 'checkpoint writer: Vec::with_capacity(checkpoint_size(variant)) and every push has a fixed length; the final assert pins len == capacity, so growth is never needed',
   'crates/aspis-r1-cost-probe/src/verifier.rs:354-371', role='*', function_regex=r'verifier3put|verifier5put_k|verifier10tx1_finish|verifier10checkpoint', src_regex=r'raw_vec/mod\.rs|vec/mod\.rs')
ex('X-VEC-GEOMETRY', 'QueryGeometry::for_range: capacities end-start, 5*(end-start), flat.len() equal the number of pushes; inverses collect from an exact-size range',
   'crates/aspis-r1-cost-probe/src/verifier.rs:184-211', role='*', function_regex=r'QueryGeometry9for_range|SpecFromIterNested', src_regex=r'raw_vec/mod\.rs|vec/mod\.rs|with_capacity')
ex('X-VEC-PUBLIC', 'R0P public_bytes: Vec::new() grown by fixed-length appends whose sequence depends only on the kind (recipient Some iff transfer, withdrawal_amount Some iff withdrawal); the growth points are therefore fixed per kind',
   'crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs:2017-2077, 1327-1361', role='stage1', function_regex=r'public_bytes', inner_regex=r'raw_vec/mod\.rs|vec/mod\.rs')
ex('X-VEC-HEAP', 'heap::filled(n): try_reserve_exact(n) then resize(n): the resize never grows; n = final_len(S2) or weights.len(), fixed',
   'crates/aspis-core/src/r0/heap.rs:5-10; crates/aspis-r1-cost-probe/src/verifier.rs:243, weights.rs:185', role='*', function_regex=r'BatchedWeights3new|Weights4pair|Vec\$LT\$T\$C\$A\$GT\$6resize|heap6filled', inner_regex=r'raw_vec/mod\.rs|vec/mod\.rs|iter/range\.rs')
ex('X-VEC-ENTRYPOINT', 'solana-program-entrypoint 2.3.0 deserialize: Vec::with_capacity(num_accounts) and one push per account',
   'solana-program-entrypoint-2.3.0/src/lib.rs:467-480', role='*', function_regex=r'solana_program_entrypoint11deserialize', src_regex=r'vec/mod\.rs|raw_vec')
ex('X-VEC-BINCODE', 'bincode 1.3.3 serialize: Vec::with_capacity(serialized_size(value)) before writing, so writes never grow',
   'bincode-1.3.3/src/internal.rs:25-36; solana-instruction-2.3.3/src/lib.rs:224-229', role='pool', function_regex=r'Instruction16new_with_bincode', src_regex=r'raw_vec/mod\.rs|vec/mod\.rs')
ex('X-SYSTEM-VARIANT', 'the SystemInstruction serialized at each call site is fixed (create_account_with_seed; or transfer, allocate_with_seed, assign_with_seed) and the seed is the 32-byte packed marker seed, so the variant and length branches of the shared serializer are positional',
   'programs/aspis-pool/src/processor.rs:385-449; nullifier.rs:72-93', role='pool', function_regex=r'Instruction16new_with_bincode')
# --- routes and constants of the transaction
ex('X-ROUTE-ADAPTER', 'verifier instruction route: stage 1 data is exactly [3,10] or [3,11], stage 2 otherwise; tags 4/5/6 (proof-buffer lifecycle) are other transactions',
   'programs/r1-cost-probe/src/r1_pool_adapter.rs:1019-1025; pool_route.rs:4', role='*', function_regex=r'r1_pool_adapter7process')
ex('X-ROUTE-POOL', 'Pool instruction route: dispatch on the 4-byte magic; the settlement is the ASQ8 pair-forest terminal',
   'programs/aspis-pool/src/processor.rs:2425-2470', role='pool', function_regex=r'aspis_pool9processor19process_instruction')
ex('X-PROOF-S2', 'proof variant: the adapter passes exactly View::proof_bytes(S2) bytes and parse_shape requires len == proof_bytes(tag), so the tag is S2 (folds()==2) in every accepted run; variant branches are constant',
   'programs/r1-cost-probe/src/r1_pool_adapter.rs:115-125, 295; crates/aspis-r1-cost-probe/src/verifier.rs:44-60, transport.rs:8-9', role='*',
   function_regex=r'verifier4View5parse|Weights4pair', ws_regex=r'verifier\.rs:(72|81)$|transport\.rs:8$|weights\.rs:252$')
ex('X-KIND-RECIPIENT', 'kind constant: recipient is Some iff transfer, withdrawal_amount Some iff withdrawal; the other arm is the other kind (a separate variant)',
   'crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs:1327-1361, 874, 1248', role='stage1', addr=['0xf6c98', '0x110048'])
# --- stored-bump fast paths: the canonical search runs only when the stored bump fails, and then rejects
ex('X-BUMP-FALLBACK-REGISTRY', 'registry/entry stored bump: on mismatch the key must equal the searched address AND registry_address_matches must hold later; with a mismatch the second check rejects, so the search arm ends in an error',
   'programs/aspis-pool/src/registry.rs:299-324, 339-370', role='pool', function_regex=r'authenticate_verifier_selection_v1', arm_callee_regex=r'find_program_address')
ex('X-BUMP-FALLBACK-LANE', 'lane stored bump: the search runs only if the stored bump does not reproduce the key; then the key differs from the canonical address (error) or data[72] differs from the canonical bump (error) or the length is wrong (error)',
   'programs/aspis-pool/src/pair_forest.rs:548-583', role='pool', function_regex=r'decode_terminal_lane_box_v1|decode_lane_account', arm_callee_regex=r'find_program_address')
ex('X-HINT-ROUTE-PAGE', 'current page: the R1 spend layout always passes Some(hint) to validate_lane_current_page; the None (search) arm is another route',
   'programs/aspis-pool/src/pair_forest.rs:1239-1258, 822-840', role='pool', function_regex=r'validate_lane_current_page', arm_callee_regex=r'find_program_address')
ex('X-HINT-ROUTE-VAULT', 'vault authority / token account: the R1 settlement passes Some(hints.vault()); the None (search) arms are the legacy route',
   'programs/aspis-pool/src/pair_forest.rs:1697-1705; vault.rs:461-512', role='pool', function_regex=r'plan_legacy_withdrawal_transfer_from_identity_v1', arm_callee_regex=r'find_program_address')
# --- arms that only reject
ex('X-ERR-ADAPTER', 'verifier error mapping: the arm builds the ProgramError returned by the instruction (the transaction fails)',
   'programs/r1-cost-probe/src/r1_pool_adapter.rs:1009; programs/r1-cost-probe/src/lib.rs:47', role='*', function_regex=r'r1_pool_adapter6stage2|first_decoded', arm_callee_regex=r'program5error|format_inner')
ex('X-ERR-MARKER', 'marker classification: a nonzero byte in a program-owned marker leads to NullifierAlreadyConsumed or InvalidNullifierMarkerAccount; both reject',
   'programs/aspis-pool/src/nullifier.rs:196-207', role='pool', function_regex=r'classify_nullifier_marker_account_v1', ws_regex=r'nullifier\.rs:20[1-6]$')
ex('X-ERR-UNIQUE', 'duplicate account keys: require_unique_accounts returns an error on the first equal pair',
   'programs/aspis-pool/src/processor.rs:200-215 (require_unique_accounts)', role='pool', function_regex=r'require_unique_accounts')
ex('X-MODE-PAGE-ZERO', 'page zero scan: in rollover the next page must be all zero (else InvalidFreshAccount); in genesis the current page is all zero by the definition of the mode; a nonzero byte belongs to another mode or rejects',
   'programs/aspis-pool/src/pair_forest.rs:806-815, 1231-1290', role='pool', function_regex=r'account_is_zeroed_program_page|plan_pair_forest_spend_layout_v1', ws_regex=r'pair_forest\.rs:81[0-5]$', applies="mode in ('rollover', 'genesis')")
ex('X-S2-GROUPED', 'grouped_inactive_pair: the S2 fast path is taken when variant == S2 and f.len() == 64*32; Weights::pair requires n == 1024 >> (2*folds) = 64 for S2, so the general grouping path never runs',
   'crates/aspis-r1-cost-probe/src/weights.rs:40, 181-182; transport.rs:8-9', role='stage2', function_regex=r'grouped_inactive_pair', ws_regex=r'weights\.rs:(39|40)$')

ex('X-PENDING-SOME', 'accumulate_with_node: on the R1 route every call passes Some(&mut pending) (tx1_finish and tx2_authenticated); the None (unbatched) arms are reached only through query()/accumulate(), which the adapter never calls',
   'crates/aspis-r1-cost-probe/src/verifier.rs:271-284, 399, 433, 455; programs/r1-cost-probe/src/r1_pool_adapter.rs (stage1 -> tx1, stage2 -> tx2_authenticated)', role='*', addr=['0x9dcf8', '0x9df48'])
ex('X-COPY-CHUNK', 'copy_tag_coordinate_dot: inside `while index < end`, chunk_end = min(index + 4, end) > index, so the inner loop test `index < chunk_end` cannot fail on entry',
   'crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs:696-699', role='stage1', addr=['0xae028'])

ex('X-WEIGHTS-S2', 'Weights::pair on S2: folds == 2 and variant == S2 fix the D, one-fold and non-S2 Libra arms; shared_two_point always holds because statement point rows 0 and 2 differ only at coordinates 6 and 7 (absorption), while factors d = 2, 3 read coordinates 5, 4, 9, 8 (TAU = [3,4,2,0,1])',
   'crates/aspis-r1-cost-probe/src/weights.rs:120-127, 181-253; crates/aspis-core/src/state_only_prefix.rs:600-614; transport.rs:4', role='stage2',
   function_regex=r'Weights4pair', ws_regex=r'weights\.rs:(18[6-9]|19[0-9]|20[0-7]|23[01]|24[4-9]|25[0-3])$', inner_regex=r'weights\.rs|transport\.rs')
ex('X-CPI-NONEMPTY', 'solana-cpi 2.2.1 invoke_signed_unchecked: StableInstruction::from(clone): the empty-data / empty-accounts arms; every CPI on the route has a nonempty data vector and account list of fixed size (system instructions, verifier ASQ8 call)',
   'solana-cpi-2.2.1/src/lib.rs:300-322; programs/aspis-pool/src/processor.rs:385-449; pair_forest_dispatch.rs:366-382', role='pool', addr=['0x60ce0', '0x60d28', '0x60d38'])

ex('X-MODE-LAYOUT', 'spend layout: the three arms are the three history modes (genesis: position 0 and a zeroed page; same-page; rollover: filled == 256 and a zeroed next page); within a variant the mode is fixed, so the arms of the other modes cannot execute',
   'programs/aspis-pool/src/pair_forest.rs:1229-1290', role='pool', function_regex=r'plan_pair_forest_spend_layout_v1', ws_regex=r'pair_forest\.rs:(1232|1233|1243|1244)$')
ex('X-PDA-SEEDS', 'create_program_address error arms (more than MAX_SEEDS seeds, or a seed longer than MAX_SEED_LEN = 32): every call on the route passes at most 5 seeds of at most 32 bytes (constant seed lists)',
   'solana-pubkey-2.4.0/src/lib.rs:912-922; seed lists in programs/aspis-pool/src/{pair_forest,registry,history,vault}.rs and programs/r1-cost-probe/src/r1_pool_adapter.rs authenticate_*', role='*', function_regex=r'Pubkey22create_program_address')

ex('X-KIND-DISPATCH', 'transition-kind dispatch: the arm is the other payment kind (transfer vs withdrawal decode, withdrawal custody plan and token CPI); the kind is a variant constant',
   'crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs:420-426, 485-492; pair_forest_semantic_terminal.rs:2057-2066; programs/aspis-pool/src/pair_forest.rs:1665-1705', role='*',
   addr=['0x19f68', '0x194b8', '0x19fd0', '0x11d540', '0x122e80', '0x1230f8', '0x70e80'])
ex('X-PREFUND', 'marker creation: account.lamports() == 0 selects create_account_with_seed, otherwise transfer/allocate/assign; prefunded or not is a variant constant',
   'programs/aspis-pool/src/processor.rs:409-447, 1641-1645', role='pool', addr=['0x3f020'])

# --- loop trip caps: N = most header executions in one entry of the loop
C = []
def cap(id_, roles, headers, N, citation, function_regex=None):
    for role in roles:
        e = dict(id=id_, role=role, addr=headers, N=N, citation=citation)
        if function_regex: e['function_regex'] = function_regex
        C.append(e)
V = ['stage1', 'stage2']
cap('C-ACC-BASIS', V, ['0x9dfa8', '0x9dfb0'], 'observed', 'verifier.rs:276: while n < a.weights.len() doubling with an inner 0..n; a.weights.len() = final_len(S2) = 64 (transport.rs:9), so the trips are constants')
cap('C-ACC-WEIGHTS', V, ['0x9e4c0', '0x9e4c8', '0x9e188', '0x9e190'], 65, 'verifier.rs:278: for j in 0..a.weights.len() = 64')
cap('C-FOURDOTS', V, ['0x45990'], 'observed', 'fast_dots.rs:17: from_fn over exactly 4 slots (a constant trip count)')
cap('C-FOURDOTS-BLOCK', V, ['0x45d38', '0x45d58'], 'observed', 'fast_dots.rs:19-21: (0..26).step_by(4) is exactly 7 blocks (a constant trip count); each min(start+4, 26)-start <= 4 terms')
cap('C-QSCAN-WORDS', ['stage1'], ['0x140820'], 9, 'r0_transcript.rs:203: for candidate in query_words(block): 8 words')
cap('C-QSCAN-CONTAINS', ['stage1'], ['0x140920', '0x140a98'], 'observed', 'r0_transcript.rs:209 accepted[..accepted_len].contains: trips are a function of accepted_len <= QUERY_COUNT-1 = 21 (r0_transcript.rs:46, 205); every accepted run passes accepted_len = 0..21, so the traced maximum per call is the maximum')
cap('C-SNAPSHOT', V + ['pool'], ['0x125e78', '0x749c8'], 21, 'pair_tree_profile.rs:466-471: level loop over the 20-entry frontier (digest_is_canonical over 8 lanes, :106-114)')
cap('C-STAGE1-CKPT', ['stage1'], ['0x369f0'], 1769, 'r1_pool_adapter.rs:940: iter().any over the checkpoint account, whose length is checkpoint_size(S2) = 1768 (r1_pool_adapter.rs:199; r1_checkpoint_tests.rs:166)')
cap('C-PARSE-RECORD', ['stage1'], ['0x48610'], 'observed', 'r1_wire.rs parse_record: every record has a fixed length and field layout (r1_wire.rs:65-83, length equality), so the trips are constants')
cap('C-APPEND-CARRY', ['stage1'], ['0x1006e8', '0x1006f8', '0x1102b8', '0x1102c8'], 21, 'pair_forest_semantic_terminal.rs:107-118 bounded_append_carry: while carry < 20')
cap('C-QM31DOT', ['stage1'], ['0x140030'], 3, 'field.rs:1478: (0..weights.len()).step_by(4) with weights.len() = 7 (state_only_poseidon.rs:525-533, ROWS: [usize; 7])')
cap('C-QM31DOT-SHORT', ['stage1'], ['0x13fdc8'], 5, 'field.rs:1455-1457: while index < weights.len() <= 4')
cap('C-COPY', ['stage1'], ['0xadfe8', '0xba0c0', '0xc1f48', '0xc2be8', '0xc2d00'], 'observed', 'pair_forest_copy_terminal.rs:543-660, 690-700, 795-802, 905-920: trips over compile-time constant tables (COPY_PATTERN_GROUP_OFFSETS, COPY_PATTERN_LOCAL_COORDINATE_GROUPS[43], COPY_TAG_COORDINATE_OFFSETS)')
cap('C-SCHEDULE', ['stage1'], ['0xd5c80'], 'observed', 'pair_forest_semantic_terminal.rs:118-130 add_preweighted::<N>: first..=last groups for a const N')
cap('C-LANE-DECODE', ['stage2'], ['0x309d0', '0x30998'], 21, 'r1_pool_adapter.rs:476-483: frontier.iter_mut() over POOL_V1_PAIR_TREE_DEPTH = 20 levels')
cap('C-WEIGHTS-PAIR', ['stage2'], ['0x74a68', '0x74bd0', '0x74c98', '0x74e80', '0x78390', '0x7be10', '0x7be78', '0x7c9b8', '0x7ca68', '0x8c2c8', '0x8efd0'], 'observed',
    'weights.rs:181-232: kinds [1,2,3,5,6], n = 64 (checked :182), tensor loops over 5 factors x 4 (:155-162), 0..4 x 0..16 (:209-217): every trip is a constant')
cap('C-FINISH', ['stage2'], ['0xa4588'], 65, 'verifier.rs:347: for (j, w) in a.weights.iter() with a.weights.len() = 64')
P = ['pool']
cap('C-ZERO-SCAN-CURRENT', P, ['0x14b58'], "8257 if mode == 'genesis' else 2", 'pair_forest.rs:806-815, 1231-1233: genesis scans the 8256-byte current page (POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES); at position 0 in same-page mode the page starts with the magic b"ASPR" (root_history.rs:14, checked history.rs:125), so the scan stops at byte 0')
cap('C-LANE-FRONTIER', P, ['0x16f80', '0x16f58', '0x182d0', '0x185f0', '0x182b8', '0x17d58'], 21, 'pair_forest.rs:606-613 and 1392-1399: loops over the 20-level frontier')
cap('C-REGISTRY-ANY', P, ['0x1908', '0x2af8'], 3, 'pair_forest_dispatch.rs:135 registry_accounts.iter().any over the two registry accounts (pair_forest.rs:1294-1297: registry_start = cursor+3, verifier_index = cursor+5)')
cap('C-ACCOUNT-VEC', P, ['0x4238', '0x4220'], 20, 'drop of the CPI account-info vector: at most the instruction account count (pair_forest.rs:1298-1307: at most 18 accounts)')
cap('C-INVOKE', P, ['0x5f9f0', '0x5fa10', '0x5f9e8', '0x60d38', '0x60ce0', '0x60d28'], 20, 'solana-program 2.3.0 invoke_signed / solana-cpi invoke_signed_unchecked: loops over the instruction metas and the passed account infos, at most 18 each (pair_forest.rs:1298-1307; processor.rs:402-407)')
cap('C-UTF8', P, ['0x88f60', '0x89068', '0x890b8', '0x88f38'], 33, 'from_utf8 over the 32-byte packed marker seed (nullifier.rs:72-93)')
cap('C-PAGE-SLOTS', P, ['0x91a0', '0x91b0'], "257 if mode == 'rollover' else 256", 'history.rs:159-163: for slot in 0..filled; filled = 256 in rollover (pair_forest.rs:1263), filled = slot+1 <= 255 in same-page (pair_forest.rs:854)')
cap('C-PAGE-ZERO', P, ['0x9240'], "1 if mode == 'rollover' else 8161", 'history.rs:164-166: zero scan of the 8256-64-32*filled unused bytes; none in rollover (filled = 256), at most 8160 in same-page (filled >= 1)')
cap('C-PAGE-WRITE', P, ['0x9628'], 3, 'history.rs:267-270: for root in roots; the settlement writes 2 roots (genesis) or 1 (rollover) (pair_forest.rs:1798-1816)')
cap('C-PAGE-APPEND', P, ['0x98c8'], 2, 'history.rs:275-279: append of one root (pair_forest.rs:1805-1809)')
K = [dict(id='K-MEMCMP', role='pool', callee_regex=r'^memcmp$', cost=20,
          citation='memcmp is an 8-instruction wrapper of the sol_memcmp_ syscall (charged max(mem_op_base_cost = 10, n/250) CU, Agave 4.2.1 execution_budget.rs:200-225); 20 covers both'),
     dict(id='K-CREATE-PDA', role='*', callee_regex=r'Pubkey22create_program_address', cost=1700,
          citation='solana-pubkey 2.4.0 lib.rs:912-940: seeds loop over at most MAX_SEEDS = 16 seeds, then the sol_create_program_address syscall (create_program_address_units = 1500)')]
# Agave 4.2.1 solana-program-runtime execution_budget.rs:200-225 (syscall_base_cost 100,
# mem_op_base_cost 10, cpi_bytes_per_unit 250, create_program_address_units 1500) and
# solana-syscalls lib.rs (log: max(base, len); mem ops: max(10, n/250) with n below 10 KiB).
SY = {'sol_log_': 300, 'sol_log_64_': 100, 'sol_log_compute_units_': 100, 'sol_memcpy_': 50, 'sol_memmove_': 50, 'sol_memset_': 50,
      'sol_memcmp_': 50, 'sol_create_program_address': 1500, 'sol_get_clock_sysvar': 200, 'sol_get_rent_sysvar': 200,
      'sol_set_return_data': 110, 'sol_get_return_data': 110, 'sol_get_stack_height': 100}
rules = dict(abort_callee_regex=ABORT, exclusions=X, loop_caps=C, callee_caps=K, syscall_caps=SY)
json.dump(rules, open(sys.argv[1], 'w'), indent=1)
print(len(X), 'exclusions')
