#!/usr/bin/env python3
"""PCXM_exposure.py (P6j): exposure of ReviewedTranscription (Aspis code) items and the CANNOT_EXTRACT set.
Run from the worktree root:  python3 -I evidence/prov-p6j-20261110/PCXM_exposure.py
Reads committed files only via `git show research:<path>`; stdlib only; no Lean, no extraction, no host.
Row counts use PCXL_recount.rows_settled_only_if (research d80d89716a0)."""
import json, re, subprocess, sys, io, collections, contextlib, lzma

REF = 'research'
E = 'evidence/'


def show(p, raw=False):
    r = subprocess.run(['git', 'show', REF + ':' + p], capture_output=True, check=True).stdout
    return r if raw else r.decode()


def J(p):
    return json.loads(show(p))


# ---- load PCXL tool (callable) without its chain output
src = show(E + 'prov-p6i-20261110/PCXL_recount.py')
ns = {'__name__': 'pcxl_loaded'}
with contextlib.redirect_stdout(io.StringIO()):
    exec(compile(src, 'PCXL_recount.py', 'exec'), ns)
cls, cone, rowdefs, SET, NOTSET = ns['cls'], ns['cone'], ns['rowdefs'], ns['SET'], ns['NOTSET']
rso = ns['rows_settled_only_if']
BASE = rso([])['baseline_rows']


def kind(k):
    c = cls.get(k)
    return 'S' if c in SET else 'N' if c in NOTSET else 'O' if c else 'U'


# ---- inputs
NPI = J(E + 'trust-final-20261110/NPI_TRUST_REACH.json')
RT = NPI['reviewed_transcription']
LEDGER = json.loads(lzma.decompress(show(E + 'ledger30-20261111/NNN_LEDGER.json.xz', raw=True)))
LROWS = [v for v in LEDGER.values() if isinstance(v, list) and len(v) == 599][0]
byrow = {r['row']: r for r in LROWS}
allkeys = sorted(cls)

# ---- name matching of frozen functions to gate keys
SUF = r'(?:_loop\d*|\.body|\.closure(?:_\d+)?|\.Insts\.\S*|_entry|_value)*$'


def fn_variants(fn):
    segs = [re.sub(r'<[^>]*>', '', s) for s in fn.split('::')]
    out = []
    for n in (len(segs), 2, 1):
        if n <= len(segs) and n >= 1:
            v = '.'.join(segs[-n:])
            if v not in out:
                out.append(v)
    return out


def match_fn(path_fn, stem_hint=None, aliases=()):
    """path_fn: 'crates/x/src/a/b.rs::Type::method'. Returns (keys, how)."""
    if '::' in path_fn:
        f, fn = path_fn.split('::', 1)
    else:
        f, fn = '', path_fn
    stem = f.split('/')[-1][:-3] if f.endswith('.rs') else ''
    stem = {'r1_pool_adapter_owned': 'owned'}.get(stem, stem)
    cand = list(aliases) or fn_variants(fn)
    for v in cand:
        short = len(v.split('.')[-1]) <= 8
        rx = re.compile(r'(?:^|[|.])' + re.escape(v) + SUF)
        hits = [k for k in allkeys if rx.search(k.split('|', 1)[1] if '|' in k else k)]
        if stem:
            sh = [k for k in hits if ('.' + stem + '.') in k.split('|', 1)[1]]
            if sh:
                return sh, 'name+stem:' + v
        if hits and not short and not stem:
            return hits, 'name:' + v
        if hits and not short and v == cand[0]:
            return hits, 'name(no stem match):' + v
    return [], 'UNMAPPED'


# ---- Table 1 items
POOL_FNS = {
    'ReviewedTranscription-POOL324': (['POOL:324'], ['programs/aspis-pool/src/pair_forest.rs::pool_v1_pair_forest_global_root_v1']),
    'ReviewedTranscription-POOL345': (['POOL:345'], ['programs/aspis-pool/src/pair_forest_dispatch.rs::SolanaPairForestVerifierRuntimeV1::get_return_data']),
    'ReviewedTranscription-POOL296': (['POOL:296'], ['programs/aspis-pool/src/nullifier.rs::pool_v1_pair_forest_marker_seed_v1']),
    'ReviewedTranscription-POOL320': (['POOL:320'], ['programs/aspis-pool/src/pair_forest.rs::next_pair_forest_lane_v1']),
    'ReviewedTranscription-POOL223': (['POOL:223'], ['crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::PoolV1PairLeafWitnessV1::validate']),
    'ReviewedTranscription-POOL332': (['POOL:332'], ['programs/aspis-pool/src/pair_forest.rs::require_exact_account_count']),
    'ReviewedTranscription-TX1:344': (['TX1:344'], ['programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage1']),
    'ReviewedTranscription-TX2:240': (['TX2:240'], ['programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage2']),
}
# (function sources for these taken from TRUST-INVENTORY-APPENDIX-DRAFT-20261027.md, sections of the same names)
CE_FN_NAMES = ['decode_lane_from_pool_release', 'Prepared::new', 'prepared_claim', 'tx2_authenticated', 'tx2_common', 'query_loop',
               'query_values', 'finish_relation', 'mark', 'verify_in_place', 'decode_k', 'semantic_boundary', 'claims', 'semantic_rounds',
               'semantic_value', 'require_distinct_accounts', 'public_bytes', 'decode_pool_v1_pair_forest_master_v1',
               'decode_pool_v1_pair_forest_checkpoint_v1', 'encode_pool_v1_pair_forest_terminal_statement_v1']


def in_ce(fn):
    last = fn.split('::')[-1]
    if last in CE_FN_NAMES or (last == 'new' and 'Prepared' in fn):
        return True
    return False


EXTRA_ITEMS = [  # listed, excluded or withdrawn (not in NPI reviewed_transcription list)
    dict(item='ReviewedTranscription-FieldDerives', rows=[], functions=[], std='STD_OR_SDK (compiler derive expansions, Rust library op; owner rule keeps)', reached='n/a'),
    dict(item='deployment_ids::deployment_id (HM-A member, op45)', rows=[], functions=[], std='STD_OR_SDK (SdkTypeModels HM-A, accepted 2026-11-10 by owner)', reached='n/a'),
    dict(item='ReviewedTranscription-PublicPreparation.public_bytes (WITHDRAWN 2026-11-10)', rows=[],
         functions=['crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::r0::Public<>::public_bytes'], reached='n/a (withdrawn; credit OPEN)'),
    dict(item='ReviewedTranscription-LaneDecode (REFUSED 2026-11-10)', rows=['TX2:217'],
         functions=['programs/r1-cost-probe/src/r1_pool_adapter.rs::decode_lane_from_pool_release'], reached='n/a (refused; op50 OPEN)'),
]

items = []
for r in RT:
    it = dict(item=r['item'], rows=list(r.get('rows') or []), functions=list(r.get('functions') or []),
              reached=r['reached'], item_root=r.get('item_root'), caveat=r.get('caveat'))
    if it['item'] in POOL_FNS:
        rws, fns = POOL_FNS[it['item']]
        it['rows_from'] = 'item name / appendix (POOL rows are not among the 599 verifier statements)' if rws[0].startswith('POOL') else 'item name'
        it['rows'] = it['rows'] or rws
        it['functions'] = fns
    items.append(it)
for x in EXTRA_ITEMS:
    x.setdefault('std', None)
    items.append(dict(x, extra=True))

# ---- consumers (rows relying): direct text mention and call-graph closure
fn2rows = collections.defaultdict(set)
for r in LROWS:
    fn2rows[r['function']].add(r['row'])
callees = {r['row']: set(c for c in r.get('canonical_callees', [])) for r in LROWS}


def closure_rows(rid, memo={}):
    if rid in memo:
        return memo[rid]
    seen, stack = set(), [rid]
    while stack:
        x = stack.pop()
        for cf in callees.get(x, ()):
            for rr in fn2rows.get(cf, ()):
                if rr not in seen and rr != x:
                    seen.add(rr)
                    stack.append(rr)
    memo[rid] = seen
    return seen


text = {rid: json.dumps(r) for rid, r in byrow.items()}


def item_ids(it):
    n = it['item']
    ids = {n}
    m = re.match(r'(NJY|NJZ|NKJ|NKM|NKI|NKL|NKU|NKY|NKR|NLH)-RT-?(\w+)', n)
    if m:
        ids.add(m.group(1) + '-RT' + m.group(2).lstrip('0'))
        ids.add(m.group(1) + '-RT' + m.group(2))
        ids.add(m.group(1) + '-RT-' + m.group(2))
    return ids


# ---- build item records
for it in items:
    own = [r for r in it['rows'] if r in byrow]
    it['own_rows_in_599'] = own
    # function keys
    fk, how = [], []
    for pf in it['functions']:
        k, h = match_fn(pf)
        fk += k
        how.append(pf.split('/')[-1] + ' -> ' + h + ' (%d)' % len(k))
    it['fn_keys_all'] = sorted(set(fk))
    it['fn_keys_in_cone'] = sorted(k for k in set(fk) if k in cone)
    it['match_how'] = how
    it['fn_key_classes'] = dict(collections.Counter(cls[k] for k in it['fn_keys_in_cone']))
    rk = sorted({k for r in own for k in rowdefs.get(r, [])})
    it['row_keys_n'] = len(rk)
    it['row_keys_unsettled_n'] = sum(1 for k in rk if kind(k) != 'S')
    it['_row_keys'] = rk
    # rows relying on the item
    direct = set(own)
    ids = item_ids(it)
    for rid, t in text.items():
        if any(i in t for i in ids if len(i) > 8):
            direct.add(rid)
    trans = set(direct)
    for rid in byrow:
        if closure_rows(rid) & direct:
            trans.add(rid)
    it['rows_relying_direct'] = sorted(direct)
    it['rows_relying_transitive_callers'] = sorted(trans)

# ---- discharge status
STATUS_TEXT = {}
for p in subprocess.run(['git', 'ls-tree', '-r', '--name-only', REF], capture_output=True, check=True).stdout.decode().split('\n'):
    if re.search(r'^evidence/prov-p[0-9a-z]+-2026110\d*/.*_STATUS\.json$|^evidence/prov-p[0-9a-z]+-20261110/.*_STATUS\.json$', p):
        STATUS_TEXT[p] = show(p)


def status_hits(fn):
    last = fn.split('::')[-1]
    last = re.sub(r'<[^>]*>', '', last)
    hits = []
    for p, t in STATUS_TEXT.items():
        if re.search(r'(?<![A-Za-z0-9_])' + re.escape(last) + r'(?![A-Za-z0-9_])', t):
            hits.append(p.split('/')[-1])
    return sorted(hits)


for it in items:
    if it.get('std'):
        it['subject'] = it['std']
        it['discharge'] = 'EXCLUDED (std/SDK)'
        continue
    it['subject'] = 'ASPIS_CODE'
    fk = it['fn_keys_in_cone']
    ce = any(in_ce(f) for f in it['functions'])
    if ce:
        it['ce'] = True
    cl = it['fn_key_classes']
    unsettled = [k for k in fk if kind(k) != 'S']
    if fk and not unsettled:
        it['discharge'] = 'DISCHARGED_BY_KEYS'
        it['discharge_note'] = 'all %d function keys in the cone are SETTLED (fresh = gate per the STATUS class of each key); the item-specific hand-reference equality is NOT separately evidenced here' % len(fk)
    elif ce:
        it['discharge'] = 'NOT: IN_CANNOT_EXTRACT'
    elif fk or it['fn_keys_all']:
        it['discharge'] = 'NOT: ATTEMPTED_KEYS_UNSETTLED'
    else:
        it['discharge'] = 'NOT: NOT_YET_ATTEMPTED (no function key found)'
    it['status_file_hits'] = {f.split('::')[-1]: status_hits(f) for f in it['functions']}

# ---- Table 2
T2 = [
    ('op50 decode_lane_from_pool_release', ['programs/r1-cost-probe/src/r1_pool_adapter.rs::decode_lane_from_pool_release'], ['decode_lane_ref'], ['TX2:217'], 'PCVV/PCWH E007/PCWO E001: early returns inside loops; contexts mismatch after patch A', None),
    ('public_bytes', ['crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::r0::Public::public_bytes'], None, [], 'PCWN item1: fresh = gate EQUALITY_PROVED (PRVEq_PB_w3.lean, PCWN_L004) with no row; NOT in CANNOT_EXTRACT any more; listed for completeness', None),
    ('verify_in_place', ['crates/aspis-r1-cost-probe/src/multiproof.rs::verify_in_place'], None, [], 'PCWH E008: breaks to outer loops not supported', None),
    ('Prepared::new / prepared_claim', ['crates/aspis-r1-cost-probe/src/verifier.rs::prepared_claim', 'crates/aspis-r1-cost-probe/src/verifier.rs::Prepared::new'], None, [], 'PCWH E008/E010: returns inside nested loops; Prepared::new Unreachable placeholder', None),
    ('decode_k', ['crates/aspis-r1-cost-probe/src/r1_wire.rs::ValidatedRecord::decode_k'], None, [], 'PCWH E010: joining region abstractions with shared loans containing borrows', None),
    ('tx2_authenticated', ['crates/aspis-r1-cost-probe/src/candidate.rs::tx2_authenticated'], None, [], 'PCWH/PCVX E013: arrow types not supported', None),
    ('tx2_common', ['crates/aspis-r1-cost-probe/src/candidate.rs::tx2_common'], None, [], 'arrow types', None),
    ('mark', ['crates/aspis-r1-cost-probe/src/verifier.rs::mark'], None, [], 'arrow types (verifier.rs 31)', None),
    ('query_loop (op6)', ['crates/aspis-r1-cost-probe/src/candidate.rs::query_loop'], None, [], 'arrow types (PCVX E013)', None),
    ('query_values', ['crates/aspis-r1-cost-probe/src/candidate.rs::query_values'], None, [], 'arrow types (PCVX E013)', None),
    ('finish_relation (op19)', ['crates/aspis-r1-cost-probe/src/verifier.rs::finish_relation'], None, [], 'arrow types + internal error (PCVX E013)', None),
    ('semantic_boundary', ['crates/aspis-r1-cost-probe/src/r1_semantic.rs::semantic_boundary'], None, [], 'PCWH E008/E009 CFailure; PCWO patch B -> arrow types', None),
    ('claims', ['crates/aspis-r1-cost-probe/src/candidate_claims.rs::claims'], None, [], 'PCWO E002: join of shared loans containing borrows', None),
    ('semantic_rounds', ['crates/aspis-r1-cost-probe/src/r1_semantic.rs::semantic_rounds'], None, [], 'PCWO E002: not emitted (depends on claims)', None),
    ('require_distinct_accounts', ['programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_distinct_accounts'], None, [], 'PCWL E001-E003: returns inside nested loops; extended Aeneas crashes', None),
    ('raw decoders op48/op49 (decode_pool_v1_pair_forest_master_v1 / checkpoint_v1)', ['crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::decode_pool_v1_pair_forest_master_v1', 'crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::decode_pool_v1_pair_forest_checkpoint_v1'], ['decode_pool_v1_pair_forest_master_v1', 'decode_pool_v1_pair_forest_checkpoint_v1'], [], 'PCVX E007/E008: could not match the contexts', None),
    ('other aspis_statement raw decoders (decode_pool_v1* name match)', [], ['decode_pool_v1'], [], 'PCVX E001-E005 closure not finished; PCVV E009/E010 no function bodies (extraction-shape miss)', 'decode_pool_v1'),
    ('op22 encode_pool_v1_pair_forest_terminal_statement_v1', ['crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::encode_pool_v1_pair_forest_terminal_statement_v1'], None, [], 'PCVX E009/E010: could not match the contexts / crash', None),
]
t2 = []
for label, fns, alias, rows, err, rx in T2:
    ks, how = [], []
    for pf in fns:
        a = None
        if alias and len(fns) == 1:
            a = alias
        elif alias and len(fns) > 1:
            a = [x for x in alias if x in pf]
        k, h = match_fn(pf, aliases=a or ())
        ks += k
        how.append(h)
    if rx:
        k = [x for x in allkeys if re.search(rx, x.split('|', 1)[1])]
        ks += k
        how.append('regex %s (%d)' % (rx, len(k)))
    t2.append(dict(item=label, functions=fns, rows_ledger=rows, err=err, how=how, keys_all=sorted(set(ks))))
# explicit module groups
cd6 = [k for k in allkeys if k.startswith('CurrentClaimDotModel|')]
sce = [k for k in allkeys if k.startswith('AspisR1SemanticCallExtraction.Funs|') and kind(k) != 'S']  # the 8 OPEN keys (PCWM); 14 settled siblings excluded
t2.append(dict(item='CurrentClaimDotModel six (prepared_claim, _dot, _dot_loop, _dot_loop.body, _loop, _loop.body)', functions=[], rows_ledger=[], err='PCWN: prepared_claim returns in nested loops; _dot* are gate-only decompositions', how=['module CurrentClaimDotModel (%d)' % len(cd6)], keys_all=cd6))
t2.append(dict(item='AspisR1SemanticCallExtraction eight (semantic_boundary, semantic_value, _entry, _loop, _loop.body ...)', functions=[], rows_ledger=[], err='PCWM E004-E006: iter().fold with fn items/closures: arrow types', how=['module AspisR1SemanticCallExtraction.Funs (%d)' % len(sce)], keys_all=sce))
# rows per key
key2rows = collections.defaultdict(set)
for r, ks in rowdefs.items():
    for k in ks:
        key2rows[k].add(r)
for t in t2:
    t['keys_in_cone'] = [k for k in t['keys_all'] if k in cone]
    t['key_classes'] = dict(collections.Counter(cls[k] for k in t['keys_in_cone']))
    rr = set()
    for k in t['keys_all']:
        rr |= key2rows.get(k, set())
    t['rows_reaching_keys_n'] = len(rr)
    t['rows_reaching_keys'] = sorted(rr)
    t['unmapped_keys'] = not t['keys_all']

# ---- item-specific keys: keys whose every reaching row is among the item's own rows or rows that call them
for it in items:
    if it.get('std'):
        it['specific_keys'] = []
        continue
    allowed = set(r for o in items if o['subject'] == 'ASPIS_CODE' for r in o['rows_relying_transitive_callers'])
    it['specific_basis'] = 'keys of the item own rows that no row outside the union of all Aspis-code RT items relying rows (own, direct, call-graph callers) reaches'
    it['specific_keys'] = sorted(k for k in it['_row_keys'] if k in cone and key2rows.get(k) and key2rows[k] <= allowed)
    it['specific_key_classes'] = dict(collections.Counter(cls[k] for k in it['specific_keys']))

# ---- counts
def counts(keyset):
    keyset = sorted(k for k in set(keyset) if k in cone)
    res = rso(keyset)
    alone = res['rows_settled_only'] - BASE
    touched = sorted(r for r, ks in rowdefs.items() if any(k in keyset and kind(k) != 'S' for k in ks))
    # settled-only rows currently: none touched (touched implies an unsettled key)
    among = len(touched) - alone
    other = set()
    for r in touched:
        for k in rowdefs[r]:
            if kind(k) == 'O' and k not in keyset:
                other.add(k)
    res2 = rso(sorted(set(keyset) | other))
    return dict(keys_in_set=len(keyset), keys_unsettled=sum(1 for k in keyset if kind(k) != 'S'),
                rows_if_all_settled=res['rows_settled_only'], baseline=BASE,
                blocked_by_these_alone=alone, rows_touched_by_unsettled_keys=len(touched), blocked_by_these_among_others=among,
                other_class_keys_sharing_rows=len(other), rows_if_set_and_sharing_other_class_settled=res2['rows_settled_only'],
                extra_rows_with_other_class=res2['rows_settled_only'] - BASE)


rt_nd = [it for it in items if it['subject'] == 'ASPIS_CODE' and it['discharge'] != 'DISCHARGED_BY_KEYS']
rt_d = [it for it in items if it['subject'] == 'ASPIS_CODE' and it['discharge'] == 'DISCHARGED_BY_KEYS']
rt_fn = set(k for it in rt_nd for k in it['fn_keys_in_cone'])
rt_row = set(k for it in rt_nd for k in it['_row_keys'] if kind(k) != 'S') | rt_fn
rt_spec = set(k for it in rt_nd for k in it['specific_keys']) | rt_fn
ce_keys = set(k for t in t2 for k in t['keys_in_cone'] if t['item'] != 'public_bytes')
CE_alone = counts(ce_keys)
RT_fn = counts(rt_fn)
RT_row = counts(rt_row)
RT_spec = counts(rt_spec)
U_fn = counts(rt_fn | ce_keys)
U_spec = counts(rt_spec | ce_keys)
U_row = counts(rt_row | ce_keys)
all_unsettled = [k for k in cone if kind(k) == 'N']
ALL_N = rso(all_unsettled)['rows_settled_only']

rely_rows_direct = sorted(set(r for it in items if it['subject'] == 'ASPIS_CODE' for r in it['rows_relying_direct']))
rely_rows_trans = sorted(set(r for it in items if it['subject'] == 'ASPIS_CODE' for r in it['rows_relying_transitive_callers']))
rely_nd_direct = sorted(set(r for it in rt_nd for r in it['rows_relying_direct']))
rely_nd_trans = sorted(set(r for it in rt_nd for r in it['rows_relying_transitive_callers']))
unmapped_items = [it['item'] for it in items if it['subject'] == 'ASPIS_CODE' and not it['fn_keys_in_cone']]

out = dict(schema='PCXM_EXPOSURE/1', target_established=False, source_ref=subprocess.run(['git', 'rev-parse', REF], capture_output=True).stdout.decode().strip(),
           tool_used='PCXL_recount.rows_settled_only_if (research d80d89716a0), final class map',
           baseline=dict(settled=sum(1 for k in cone if kind(k) == 'S'), not_settled=sum(1 for k in cone if kind(k) == 'N'), other=sum(1 for k in cone if kind(k) == 'O'), rows_settled_only=BASE, rows_if_all_not_settled_settled=ALL_N),
           counts=dict(RT_fn_keys=RT_fn, RT_item_specific_keys=RT_spec, UNION_item_specific_keys=U_spec, RT_row_keys_upper_bound=RT_row, CE=CE_alone, UNION_fn_keys=U_fn, UNION_row_keys_upper_bound=U_row),
           rows_relying=dict(items_total=len([i for i in items if i['subject'] == 'ASPIS_CODE']), not_discharged_items=len(rt_nd), discharged_by_keys=[i['item'] for i in rt_d],
                             all_items_direct=len(rely_rows_direct), all_items_with_callers=len(rely_rows_trans),
                             not_discharged_direct=len(rely_nd_direct), not_discharged_with_callers=len(rely_nd_trans)),
           unmapped_items_no_function_key=unmapped_items,
           table1=[{k: v for k, v in it.items() if not k.startswith('_')} for it in items], table2=t2)
json.dump(out, open('evidence/prov-p6j-20261110/PCXM_EXPOSURE.json', 'w'), indent=1)
print(json.dumps(dict(baseline=out['baseline'], counts=out['counts'], rows_relying=out['rows_relying'], unmapped=len(unmapped_items)), indent=1))
print([ (i['item'],len(i['specific_keys'])) for i in items if i['subject']=='ASPIS_CODE'])
