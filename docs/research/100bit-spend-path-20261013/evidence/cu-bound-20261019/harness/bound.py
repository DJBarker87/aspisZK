#!/usr/bin/env python3
"""Compose B_stage1 and B_settlement per kind (PREREG method step 3) and emit sites.json.

B_tx = max saved-fixture CU for the transaction + sum of site maxima, where the
site maxima come from (i) ELF value-branch rules R1/R3 (aggregate_elf.py),
(ii) data-dependent loops (function-level instruction range over traces that
reach the loop's trip-count extremes), (iii) source-level sites costed
analytically, (iv) syscall sites with Agave 4.2.1 constants.
"""
import json, re, sys, collections
A = sys.argv[1]; OUT = sys.argv[2]; SWEEP = sys.argv[3:]  # sweep.jsonl files
FIX = {'transfer': dict(stage1=1199687, settlement=1174671), 'withdrawal': dict(stage1=1198386, settlement=1188496)}
CPA = 1500  # create_program_address_units, solana-program-runtime-4.2.1 execution_budget.rs:203
FIND_MAX_EXTRA = 254 * CPA  # solana-syscalls-4.2.1 lib.rs:893-929 (for _ in 0..u8::MAX)

UNMAPPED_CLASSES = [
    ('U1-panic-or-abort', r'panicking|panic_bounds|index_len_fail|index_order_fail|unwrap_failed|handle_alloc_error|raw_vec12handle_error|assert_failed|len_mismatch|panic_already|panic_fmt'),
    ('U2-vec-growth-fixed-length', r'do_reserve_and_handle|grow_one|__rust_realloc'),
    ('U3-route-or-kind-constant', r'transfer_statement|private_transfer|lifecycle_|r1_pool_adapter6stage[12]|first_decoded|entrypoint11deserialize|_with_runtime_v1|withdrawal|vault|require_token_program_account|process_'),
    ('U4-error-constructor', r'program_error|ProgramError|5error17|create_program_address|format_inner|registry_v1|registry_entry_v1|validate_|decode_pool_v1_nullifier_marker|drop_in_place'),
    ('U5-proof-variant-constant', r'opening8inactive|twofold_libra|dense_point_pair|try_from_fn17h2570dfa09e326f62'),
    ('U6-circle-fallback', r'circle_fallback_point'),
    ('U7-marker-prefunded-path', r'system_interface|create_or_allocate_pda_with_rent'),
]
def classify(callees):
    tags = set()
    for c in callees or ['<none>']:
        for tag, rx in UNMAPPED_CLASSES:
            if re.search(rx, c): tags.add(tag); break
        else: tags.add('RESIDUAL:' + c[:80])
    return sorted(tags)

sweep = collections.defaultdict(list)
for f in SWEEP:
    for l in open(f):
        r = json.loads(l)
        if r.get('exit_status') == 0: sweep[r['kind']].append(r)

sites = []; result = {}
for kind in ['transfer', 'withdrawal']:
    comp = {}
    for role in ['stage1', 'stage2', 'pool']:
        agg = json.load(open(f'{A}/{role}-{kind}-agg.json')); raw = json.load(open(f'{A}/{role}-{kind}.json'))
        t = agg['totals']
        comp[f'{role}.elf_R1'] = t.get('R1', 0); comp[f'{role}.elf_R3'] = t.get('R3', 0)
        sites.append(dict(id=f'ELF-R1-{role}-{kind}', kind=kind, tx='stage1' if role == 'stage1' else 'settlement',
                          source='value-dependent conditional branches (both arms observed, decision sequence varies)',
                          elf=f'{t.get("R1#", 0)} branch sites in {role} ELF; top: ' + ', '.join(f"{r['addr']} {r['function'][:60]} {r['per_exec']}x{r['max_count']}" for r in agg['top_sites'] if r['rule'] == 'R1')[:600],
                          max_extra_cu=t.get('R1', 0), max_count='per site: max dynamic count over traces (counts fixed by code except split/loop sites)',
                          cap='per-branch slack = longest - shortest instruction path to the immediate post-dominator; 1 CU per SBF instruction'))
        sites.append(dict(id=f'ELF-R3-{role}-{kind}', kind=kind, tx='stage1' if role == 'stage1' else 'settlement',
                          source='one-sided conditional branches whose unobserved arm may be longer (rare value branches, e.g. final canonical reduction)',
                          elf=f'{t.get("R3#", 0)} branch sites', max_extra_cu=t.get('R3', 0), max_count='max dynamic count over traces',
                          cap='static unobserved-arm longest path minus observed-arm shortest path'))
        # data-dependent loops: function-level instruction range over traces
        fnames = {l['function'] for l in agg['data_dependent_loops']}
        rng = sum(max(raw['functions'][f]['per_trace']) - min(raw['functions'][f]['per_trace']) for f in fnames if f in raw['functions'])
        comp[f'{role}.loops'] = rng
        if fnames:
            sites.append(dict(id=f'LOOP-{role}-{kind}', kind=kind, tx='stage1' if role == 'stage1' else 'settlement',
                              source='loops whose trip count depends on the lane position (trailing ones / zero bits of next_leaf_index, root-page fill and page mode)',
                              elf='; '.join(sorted(f[:70] for f in fnames)), max_extra_cu=rng,
                              max_count='trip counts <= POOL_V1_PAIR_TREE_DEPTH = 20 (format.rs:28) and <= POOL_V1_ROOT_HISTORY_CAPACITY = 256 (root_history.rs:16-17); traced runs include pairs 0 (all zero bits), 2^20-1 (all ones), page fill 0 and 255',
                              cap='max - min instruction count of the containing functions over traces that reach both trip-count extremes'))
        cls = collections.Counter()
        for u in agg['unmapped']:
            for tag in classify(u['callees']): cls[tag] += 1
        comp[f'{role}.unmapped_classes'] = dict(cls)
    # analytical source-level sites
    s1 = [r for r in sweep[kind]]
    s11 = [r['stage1_cu'] for r in s1 if (r.get('inputs') or {}).get('split') == 11]
    s10 = [r['stage1_cu'] for r in s1 if (r.get('inputs') or {}).get('split') == 10]
    split_extra = (max(s11) - min(s10)) if s11 and s10 else None
    comp['split'] = split_extra
    comp['query_scan'] = 42 * 200
    comp['circle_fallback'] = 2 * 1970
    comp['marker_prefunded'] = 5000
    praw = json.load(open(f'{A}/pool-{kind}.json'))
    comp['bump_search_calls'] = max(s.get('sol_try_find_program_address', {}).get('count', 0) for s in praw['syscalls'])
    comp['bump_search_calls_per_trace'] = [s.get('sol_try_find_program_address', {}).get('count', 0) for s in praw['syscalls']]
    comp['bump_search'] = comp['bump_search_calls'] * FIND_MAX_EXTRA
    B1 = FIX[kind]['stage1'] + split_extra + comp['stage1.elf_R1'] + comp['stage1.elf_R3'] + comp['stage1.loops'] + comp['query_scan'] + comp['circle_fallback']
    B2 = (FIX[kind]['settlement'] + comp['stage2.elf_R1'] + comp['stage2.elf_R3'] + comp['stage2.loops']
          + comp['pool.elf_R1'] + comp['pool.elf_R3'] + comp['pool.loops'] + comp['marker_prefunded'] + comp['bump_search'])
    B2_without_bump = B2 - comp['bump_search']
    sw1 = max(r['stage1_cu'] for r in s1); sw2 = max(r['settlement_cu'] for r in s1)
    result[kind] = dict(components=comp, B_stage1=B1, B_settlement=B2, B_settlement_excluding_bump_search=B2_without_bump,
                        swept_max_stage1=sw1, swept_max_settlement=sw2, runs=len(s1),
                        sweep_le_bound=dict(stage1=sw1 <= B1, settlement=sw2 <= B2))
    sites += [
        dict(id=f'S-SPLIT-{kind}', kind=kind, tx='stage1', source='programs/r1-cost-probe/src/pool_route.rs:4 admits [3,10] and [3,11]; verifier.rs tx1_finish runs k queries',
             elf='verifier::tx1_finish / query_with_geometry loop', max_extra_cu=split_extra, max_count=1,
             cap='k in {10,11} (pool_route.rs:4, r1_pool_adapter.rs stage1); extra = max swept stage1 at k=11 - min swept stage1 at k=10'),
        dict(id=f'S-QSCAN-{kind}', kind=kind, tx='stage1', source='aspis-core/src/r0_transcript.rs:202-214 QueryScan::scan (duplicate draws)',
             elf='aspis_core::r0_transcript::QueryScan::scan (547-931 instr per 8-word call observed)', max_extra_cu=comp['query_scan'], max_count=42,
             cap='draws <= QUERY_MAX_DRAWS = 64 (r0_transcript.rs:48), 22 accepted minimum; 200 CU per extra draw (contains over <= 22 u32 plus loop) is an upper bound'),
        dict(id=f'S-CIRCLE-{kind}', kind=kind, tx='stage1', source='aspis-core/src/r0_transcript.rs circle_sample fallback; transcript.rs:286-296',
             elf='aspis_core::transcript::circle_fallback_point (never executed in traces)', max_extra_cu=comp['circle_fallback'], max_count=2,
             cap='two circle rows (25, 26); extra <= max inclusive cost of secure_ood_circle_point_from_parameter = 1970 instr (traced)'),
        dict(id=f'S-BUMP-{kind}', kind=kind, tx='settlement', source='aspis-pool find_program_address: nullifier.rs:32 (marker, twice: plan + replan), history.rs:38 (current page; next page on rollover), pair_forest.rs:208/222/233 (master/lane/checkpoint), registry.rs, vault.rs',
             elf=f"aspis_pool sol_try_find_program_address calls per settlement (traced, per trace): {comp['bump_search_calls_per_trace']}",
             max_extra_cu=comp['bump_search'], max_count=comp['bump_search_calls'],
             cap='Agave solana-syscalls-4.2.1 lib.rs:893-929: 1500 CU per bump attempt, at most 255 attempts; accepted => <= 254 failed attempts => <= 381,000 CU per call'),
        dict(id=f'S-MARKER-PREFUNDED-{kind}', kind=kind, tx='settlement', source='aspis-pool processor.rs create_or_allocate_pda_with_rent: prefunded marker PDA uses transfer+allocate+assign',
             elf='solana_system_interface transfer/allocate/assign arms never executed in traces', max_extra_cu=5000, max_count=1,
             cap='at most 3 System CPIs instead of 1: 2 x (invoke_units 946 + System builtin + CPI byte charges) < 5000 (upper bound, not traced)'),
    ]
json.dump(dict(result=result, method='PREREG-CU-UPPER-BOUND-20261019 steps 1-3'), open(OUT + '/bound.json', 'w'), indent=1)
json.dump(sites, open(OUT + '/sites.json', 'w'), indent=1)
print(json.dumps(result, indent=1))
