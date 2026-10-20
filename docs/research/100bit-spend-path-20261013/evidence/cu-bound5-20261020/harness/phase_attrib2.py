#!/usr/bin/env python3
"""Step 6 consistency. Verifier: every cu-profiling phase whose CU varies across the profiled
runs of a (kind, split, tx) group must be covered by listed sites of the functions that run in
that phase: range <= sum of the sites' traced spreads (over the traced runs of the group) plus
their counted residuals. Pool: every function whose instruction count varies between traced
runs of a settlement variant must contain a listed site with a nonzero spread or residual.
usage: phase_attrib2.py <analysis dir> <profile-phases.json> <out.json>"""
import json, re, sys, collections
A, PROF, OUT = sys.argv[1:4]
prof = json.load(open(PROF)); runs = json.load(open(f'{A}/runs.json')); spv = json.load(open(f'{A}/sites-per-variant.json'))
PH = [  # (tx, phase regex, function regex) - the first method's phase map, extended
 ('stage1', r'^r1:semantic$', r'r1_semantic|r1_wire|pair_forest_semantic_terminal|pair_forest_copy_terminal|state_only|semantic|sampler|circle|try_from_fn|public_bytes|field|poseidon|from_fn'),
 ('stage1', r'^r1:prepare$', r'Prepared|sampler|transcript|r0_transcript|QueryScan|prepared_claim|EbyKDot|fast_pairing|powers|field'),
 ('stage1', r'^r1:(merkle|query):', r'candidate12batch_merkle|candidate10tx2_common|candidate3tx1|multiproof|merkle_path|private_leaf|four_dots|query_with_geometry|accumulate|fold|BatchedWeights|QueryGeometry|fast_dots|field|from_fn'),
 ('stage1', r'^r1:(parsed|checkpoint-write)', r'compact|canonical_scan|View|parse|echeck|checkpoint|tx1|stage1|decode|validate|encode|first|put'),
 ('stage2', r'^r1:parsed', r'r1_pool_adapter|decode|validate|encode|View|authenticate|scan_proof|reconstruct|asq8|stage2|pair_forest|payment|verifier_registry|lane|echeck|parse'),
 ('stage2', r'^r1:(checkpoint-read)', r'resume|Reader|powers|checkpoint|QueryGeometry|BatchedWeights|from_le'),
 ('stage2', r'^r1:(merkle|query):', r'candidate12batch_merkle|candidate10tx2_common|candidate3tx1|multiproof|merkle_path|private_leaf|four_dots|query_with_geometry|accumulate|fold|BatchedWeights|fast_dots|field|from_fn'),
 ('stage2', r'^r1:(relation|final)', r'finish_relation|weights|Weights|polynomial|EbyKDot|fast_pairing|libra|scalar_factor|try_from_fn|field'),
]
def spreads(role, kind, split):
    d = json.load(open(f'{A}/{role}.json'))
    idx = [i for i, t in enumerate(d['traces']) if runs[t['label']]['kind'] == kind and runs[t['label']]['split'] == split]
    out = collections.Counter()
    for k, b in enumerate(d['branches']):
        if 'arms' not in b: continue
        L = [a['L'] if isinstance(a['L'], int) else 0 for a in b['arms']]
        est = [d['traces'][i]['taken'][k] * L[1] + (d['traces'][i]['counts'][k] - d['traces'][i]['taken'][k]) * L[0] for i in idx]
        if est: out[b['function']] += max(est) - min(est)
    for l in d['loops']:
        c = [l['per_trace'][i][0] for i in idx]
        if c and l['W_iter']: out[l['function']] += (max(c) - min(c)) * l['W_iter']
    return out
resid = collections.defaultdict(collections.Counter)
for e in spv:
    for s in e['sites']:
        if s['residual']: resid[(e['role'], e['variant'][0], e['variant'][1])][s['function']] = max(resid[(e['role'], e['variant'][0], e['variant'][1])][s['function']], s['residual'])
rows = []; cache = {}
for group, phases in prof.items():
    kind, split, tx = group.split('/'); split = int(split)
    if (tx, kind, split) not in cache: cache[(tx, kind, split)] = spreads(tx, kind, split)
    sp = cache[(tx, kind, split)]; rs = resid[(tx, kind, split)]
    for ph, v in phases.items():
        if not v['varies']: continue
        base = ph.split('#')[0]; m = [p for p in PH if p[0] == tx and re.search(p[1], base)]
        rng = v['max'] - v['min']
        if not m: rows.append(dict(group=group, phase=ph, range=rng, covered=False, why='no phase map')); continue
        fr = m[0][2]
        listed = sum(x for f, x in sp.items() if re.search(fr, f)) + sum(x for f, x in rs.items() if re.search(fr, f))
        rows.append(dict(group=group, phase=ph, range=rng, listed_spread_plus_residual=listed, covered=rng <= listed))
# Pool: function-level attribution within each settlement variant
d = json.load(open(f'{A}/pool.json')); fnames = d['functions']
groups = collections.defaultdict(list)
for i, t in enumerate(d['traces']):
    m = runs[t['label']]; groups[(m['kind'], m['split'], m['mode'], m['prefund'])].append(i)
listed_fn = collections.defaultdict(set)
for k, b in enumerate(d['branches']):
    if 'arms' not in b: continue
    for V, idx in groups.items():
        cs = {(d['traces'][i]['counts'][k], d['traces'][i]['taken'][k]) for i in idx}
        if len(cs) > 1: listed_fn[V].add(b['function'])
for l in d['loops']:
    for V, idx in groups.items():
        if len({tuple(l['per_trace'][i]) for i in idx}) > 1: listed_fn[V].add(l['function'])
pool_rows = []
for V, idx in groups.items():
    per = collections.defaultdict(list)
    for i in idx:
        for f, c in d['traces'][i]['per_fn'].items(): per[fnames[int(f)] if f not in ('None',) else '<unmapped>'].append(c)
    for f, cs in per.items():
        full = cs + [0] * (len(idx) - len(cs))
        if max(full) != min(full):
            pool_rows.append(dict(V=list(V), function=f, range=max(full) - min(full), explained=f in listed_fn[V]))
bad = [r for r in rows if not r['covered']]; pbad = [r for r in pool_rows if not r['explained']]
json.dump(dict(verifier=rows, verifier_unexplained=bad, pool=pool_rows, pool_unexplained=pbad), open(OUT, 'w'), indent=1)
print('verifier varying phases', len(rows), 'unexplained', len(bad)); [print('  ', r) for r in bad[:10]]
print('pool varying functions (per variant)', len(pool_rows), 'unexplained', len(pbad)); [print('  ', r) for r in pbad[:10]]
