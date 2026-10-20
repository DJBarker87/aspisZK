#!/usr/bin/env python3
"""Write sites.json (every executed branch site and loop, classified per variant) and
variants.json (step-1 measurements with B per variant).
usage: make_deliverables.py <analysis dir> <rules.json> <variants-measured.json> <out dir>"""
import json, sys, re, collections
A, RULES, VM, OUT = sys.argv[1:5]
spv = json.load(open(f'{A}/sites-per-variant.json')); rules = json.load(open(RULES)); bound = json.load(open(f'{A}/bound.json'))
vm = json.load(open(VM))
lines = {}
for r in ['stage1', 'stage2', 'pool']:
    lines[r] = json.load(open(f'{A}/lines-{r}.json'))
    for extra in (f'{A}/needlines-{r}.json', f'{A}/hdrlines-{r}.json'):
        try: lines[r].update(json.load(open(extra)))
        except FileNotFoundError: pass
def src(role, addr):
    fr = (lines[role].get(addr) or {}).get('frames') or []
    ws = [f[1] for f in fr if 'rust/library' not in f[1] and '.cargo' not in f[1]]
    return dict(innermost=fr[0][1].split('/library/')[-1] if fr else None, workspace=ws[:3],
                mapped=bool(fr), note=None if fr else (lines[role].get(addr) or {}).get('reason', 'not in line map'))
def dem(n): return re.sub(r'17h[0-9a-f]{16}E$', '', n)
# the variant that sets B per transaction and kind
dom = {}
for tx in ['stage1', 'settlement']:
    for kind in ['transfer', 'withdrawal']:
        V = max((V for V in bound['B'][tx] if json.loads(V)[0] == kind), key=lambda V: bound['B'][tx][V]['B'])
        dom[(tx, kind)] = json.loads(V)
sites = {}; trivial = collections.defaultdict(lambda: collections.defaultdict(list))
for e in spv:
    role, V = e['role'], e['variant']; tx = 'stage1' if role == 'stage1' else 'settlement'
    is_dom = V == dom[(tx, V[0])]
    for s in e['sites']:
        key = (role, s['addr'])
        ent = sites.setdefault(key, dict(role=role, elf_addr=s['addr'], function=dem(s['function']), cls=s.get('cls'), rules=collections.Counter(),
                                         residual_max=0, notes=set()))
        ent['rules'][s['rule']] += 1; ent['residual_max'] = max(ent['residual_max'], s['residual'])
        for n in s.get('notes') or []: ent['notes'].add(n)
        if s.get('cap'): ent['notes'].add('cap:' + s['cap'])
        if s.get('source_cap_id'): ent['notes'].add('source-cap:' + s['source_cap_id'])
        if is_dom:
            d = dict(variant=V, residual=s['residual'], count_w=s.get('count_w', s.get('header_count_w')))
            if 'arms_longest' in s and all(isinstance(x, int) for x in s['arms_longest']) and s.get('count_w') is not None:
                Lf, Lt = s['arms_longest']; cw, tw = s['count_w'], s['taken_w']
                d['cost_in_worst_input'] = tw * Lt + (cw - tw) * Lf
                d['max_cost'] = d['cost_in_worst_input'] + s['residual']
            elif s.get('cls') == 'loop' and s.get('W_iter'):
                d['cost_in_worst_input'] = s['header_count_w'] * s['W_iter']; d['max_cost'] = d['cost_in_worst_input'] + s['residual']
                d.update(N=s.get('N'), entries_w=s.get('entries_w'), W_iter=s['W_iter'])
            ent.setdefault('in_dominating_variant', {})[V[0]] = d
cite = {r['id']: dict(reason=r.get('reason'), citation=r['citation']) for r in rules['exclusions'] + rules['loop_caps'] + rules['callee_caps']}
out_sites = []
for (role, addr), ent in sorted(sites.items()):
    nontriv = ent['residual_max'] or any(n.split(':')[1] in ('excluded',) or n.startswith(('cap:', 'source-cap:')) for n in ent['notes'] if ':' in n)
    if not nontriv:
        trivial[role][','.join(sorted(ent['rules']))].append(addr); continue
    ent['rules'] = dict(ent['rules']); ent['notes'] = sorted(ent['notes']); ent['source'] = src(role, addr)
    ids = sorted({n.split(':')[-1] for n in ent['notes'] if 'excluded' in n} | {n.split(':',1)[1] for n in ent['notes'] if n.startswith(('cap:', 'source-cap:'))})
    ent['exclusion_or_cap_citations'] = {i: cite[i] for i in ids if i in cite}
    out_sites.append(ent)
json.dump(dict(method='PREREG-CU-UPPER-BOUND-2-20261019 steps 2-5', dominating_variants={f'{k[0]}/{k[1]}': v for k, v in dom.items()},
               rule_legend=dict(R1='both arms taken, decisions vary: residual = per execution (longest arm - longest of taken arm)',
                                R0='both arms taken, decision sequence identical in all >= 3 traced runs of the variant: positional, 0',
                                R2='one arm never taken in the variant and not longer than the taken arm: 0',
                                R3='one arm never taken in the variant, counted at its longest path (method step 4)',
                                R4='never-taken arm whose every path calls an abort routine: the transaction fails (rejected, out of scope)',
                                X='never-taken arm excluded by a code citation (exclusion_or_cap_citations)',
                                LC='loop-control branch: in-iteration choice; trips and exits are costed at the loop',
                                L0='loop with identical header/back-edge counts in all traced runs of the variant and no counted arm that lengthens it',
                                L1='loop with a cited trip cap N per entry: (N * entries_w - header_count_w) * W_iter + exit residual',
                                LA='loop entered only through a counted never-taken arm, at its cited cap'),
               sites=out_sites, trivial_sites={r: dict(v) for r, v in trivial.items()},
               rules_cited=cite, source_level_sites=bound['source_sites']),
          open(f'{OUT}/sites.json', 'w'), separators=(',', ':'))
var = dict(stage1=[], settlement=[])
for x in vm['stage1']:
    V = json.dumps([x['kind'], x['split']]); b = bound['B']['stage1'][V]
    var['stage1'].append(dict(x, traced_worst=b['worst'], traced_worst_cu=b['worst_cu'], residual_elf=b['residual_elf'], residual_source=b['residual_qscan'], residual_parent_sha=b['residual_parent_sha'], B=b['B']))
for x in vm['settlement']:
    V = json.dumps([x['kind'], x['split'], x['mode'], x['prefund']]); b = bound['B']['settlement'][V]
    var['settlement'].append(dict(x, traced_worst=b['worst'], traced_worst_cu=b['worst_cu'], residual_stage2=b['residual_stage2'], residual_pool=b['residual_pool'], residual_parent_sha=b['residual_parent_sha'], B=b['B']))
json.dump(dict(var, per_kind=bound['per_kind'], verdict=bound['verdict']), open(f'{OUT}/variants.json', 'w'), indent=1)
print('sites (nontrivial)', len(out_sites), 'trivial', {r: sum(len(x) for x in v.values()) for r, v in trivial.items()})
