#!/bin/bash
# PCXD_l187.sh: PCXD_L187_RECONCILE.json
cd /Users/dominic/ZK/.worktrees/pc-prov-p6r/evidence/prov-p6r-20261110
python3 -I -B - <<'PY'
import sys, json, lzma, collections
sys.path.insert(0, '.')
import PCXD_lib as L
man = L.J('replay-l187-20261109/L187_SOURCE_MANIFEST.json'); clo = L.JX('replay-l187-20261109/L187_CLOSURE.json.xz')
pco_all = L.J('prov-p0-20261109/PCO_PARTITION.json'); pco = pco_all['modules']
fixes = {}
for l in open(L.SCR.rsplit('/', 1)[0] + '/in/L187_SOURCE_FIXES.jsonl'):
    o = json.loads(l); fixes[o['module']] = o
pcuf = L.J('prov-p2j-20261110/PCUJ_ALL_STATUS.json')['modules']
def pmod(label):
    if label in pco: return label
    for suf in ('_Funs', '_Types'):
        if label.endswith(suf) and label[:-len(suf)] + '.' + suf[1:] in pco: return label[:-len(suf)] + '.' + suf[1:]
proved_by_mod = collections.Counter()
for label, d in pcuf.items():
    m = pmod(label)
    for r in d.values():
        if r['status'] in ('EQUALITY_PROVED', 'EQUALITY_DOMAIN', 'CONDITIONAL_ON_BINDING'): proved_by_mod[m or label] += 1
clomod = {x['module']: x for x in clo['modules']}
def ours(m):
    p = pco.get(m)
    if not p: return None
    return dict(shas=[c['sha256'] for c in p['candidates']], group=p['group'], subgroup=p['subgroup'], compiled_source_ambiguous=p.get('compiled_source_ambiguous', False),
                shadow=[x['sha256'] for x in p.get('shadow_candidates', [])][:6], pilot_correction=p.get('pilot_correction'))
def cmp(m, l187_sha, how):
    o = ours(m)
    if o is None: return dict(verdict='MODULE_NOT_IN_EMITTED_PARTITION', note='not an Aeneas-emitted gate module in PCO_PARTITION (hand-written/proof module)')
    if l187_sha is None: return dict(verdict='NO_L187_SOURCE_HASH', ours=o)
    ag = l187_sha in o['shas']
    return dict(verdict='AGREE' if ag else 'DISAGREE', l187_source_sha256=l187_sha, l187_source_basis=how, our_candidate_sha256=o['shas'], group=o['group'], subgroup=o['subgroup'], compiled_source_ambiguous=o['compiled_source_ambiguous'],
                shadow_candidates=o['shadow'], pilot_correction=o['pilot_correction'], provenance_equalities_credited_for_module=proved_by_mod.get(m, 0))
def l187sha(x):
    r = x.get('recovered')
    if r and r.get('sha256'): return r['sha256'], 'recovered by receipt/object identity'
    cs = x.get('candidate_source')
    if cs and cs.get('sha256'): return cs['sha256'], 'latest successful receipt candidate (object identity NOT shown)'
    return None, None
A = []   # (a) the 14
unrec = man['summary']['unrecovered']
for m in unrec:
    x = [y for y in man['modules'] if y['module'] == m][0]; s, how = l187sha(x)
    A.append(dict(module=m, l187_status='UNRECOVERED', l187_candidate=x.get('candidate_source'), reason=x.get('reason'), **cmp(m, s, how)))
B = []   # (b) 42
for m in man['summary']['recovered_but_committed_copy_at_module_path_differs_or_absent']:
    x = [y for y in man['modules'] if y['module'] == m][0]; s, how = l187sha(x)
    B.append(dict(module=m, l187_status=x['status'], committed_copies=[(c['path'], c['matches_recovered']) for c in (x.get('committed_copies_at_module_path') or [])][:4], **cmp(m, s, how)))
C = []   # (c) 37 no source + 122 several
for x in clo['modules']:
    st = x.get('source_status')
    if st in ('unique', None): continue
    m = x['module']; cs = [c['sha256'] for c in x.get('committed_sources', [])]
    mm = [y for y in man['modules'] if y['module'] == m]
    s = l187sha(mm[0])[0] if mm else None
    o = ours(m)
    rec = dict(module=m, closure_source_status=st, n_committed_sources=len(cs), in_unified_manifest=bool(mm), l187_resolved_sha256=s)
    if o is None: rec['verdict'] = 'MODULE_NOT_IN_EMITTED_PARTITION'
    else:
        inter = sorted(set(cs) & set(o['shas']))
        rec.update(our_candidate_sha256=o['shas'], group=o['group'], compiled_source_ambiguous=o['compiled_source_ambiguous'], candidate_among_committed_sources=bool(inter))
        rec['verdict'] = ('AGREE' if s and s in o['shas'] else 'DISAGREE') if s else ('OUR_CANDIDATE_IS_ONE_OF_THE_COMMITTED_SOURCES' if inter else 'NO_COMMITTED_SOURCE_EQUALS_OUR_CANDIDATE' if cs else 'NO_COMMITTED_SOURCE')
    C.append(rec)
D = []   # addendum: eight SOURCE_PATH_DIFFERS
for m, f in fixes.items():
    ns = f['new_source']['sha256']; os_ = f['old_source']['sha256']; o = ours(m)
    r = dict(module=m, source_fix_reason=f['why'], old_committed_source=f['old_source'], recovered_source=f['new_source'], record_status='SOURCE_PATH_DIFFERS')
    if o is None: r.update(verdict='MODULE_NOT_IN_EMITTED_PARTITION', note='not in the 373 emitted modules (hand-written module); no compiled_source candidate or control of ours exists')
    else:
        r.update(our_candidate_sha256=o['shas'], group=o['group'], compiled_source_ambiguous=o['compiled_source_ambiguous'], shadow_candidates=o['shadow'], pilot_correction=o['pilot_correction'],
                 verdict='AGREE' if ns in o['shas'] else 'AGREE_VIA_PCO_SHADOW_CANDIDATE_PRIMARY_CANDIDATE_IS_THE_OLD_COMMITTED_SOURCE' if (ns in o['shadow'] and os_ in o['shas']) else 'OUR_CANDIDATE_IS_THE_OLD_COMMITTED_SOURCE' if os_ in o['shas'] else 'DISAGREE', provenance_equalities_credited_for_module=proved_by_mod.get(m, 0))
    D.append(r)
V = lambda L_: dict(collections.Counter(x['verdict'] for x in L_))
out = dict(schema='PCXD_L187_RECONCILE/1', target_established=False,
  inputs=dict(manifest='replay-l187-20261109/L187_SOURCE_MANIFEST.json (research_head ' + man['research_head'][:11] + ')', closure='replay-l187-20261109/L187_CLOSURE.json.xz',
              source_fixes='L187_SOURCE_FIXES.jsonl read from branch codex/cx-integrate-20261107 (not yet on research when read); eight records', partition='prov-p0-20261109/PCO_PARTITION.json'),
  comparison_limit='Source comparison is by sha256 of the source file text (declaration-level object identity is what L187 established; .olean bytes embed the invocation path). No object comparison was run by this job.',
  a_unrecovered_14=dict(verdicts=V(A), items=A), b_versioned_or_renamed_42=dict(verdicts=V(B), items=B),
  c_no_source_or_several_sources=dict(n=len(C), verdicts=V(C), items=C), d_lead_addendum_eight_source_path_differs=dict(verdicts=V(D), items=D),
  disagreements=[dict(group=g, module=x['module'], verdict=x['verdict']) for g, L_ in (('a', A), ('b', B), ('c', C), ('d', D)) for x in L_ if x['verdict'] in ('DISAGREE', 'NO_COMMITTED_SOURCE_EQUALS_OUR_CANDIDATE', 'OUR_CANDIDATE_IS_THE_OLD_COMMITTED_SOURCE') or x['verdict'].startswith('AGREE_VIA')])
json.dump(out, open('PCXD_L187_RECONCILE.json', 'w'), indent=1)
print(V(A), V(B), V(C), V(D), len(out['disagreements']))
PY
