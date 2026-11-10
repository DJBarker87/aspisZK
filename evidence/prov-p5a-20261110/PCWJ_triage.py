#!/usr/bin/env python3
"""PCWJ_triage.py: triage of the OPEN definitions of PCXH_PROVENANCE (reads committed files via git show research/HEAD).
Usage: python3 -I PCWJ_triage.py [outdir]"""
import json, subprocess, sys, re, collections
REF = 'HEAD'
def show(p): return subprocess.run(['git','show',REF+':'+p],capture_output=True,check=True).stdout.decode()
E = 'evidence/'
P = json.loads(show(E+'prov-p6w-20261110/PCXH_PROVENANCE.json'))['per_definition_class']
C = json.loads(show(E+'prov-p6z-20261110/PCXJ_COUNTS.json'))   # P2k,P3u,P3w,P3v,P3x credits applied by PCXJ_recount.py
U = json.loads(show(E+'prov-p2j-20261110/PCUJ_ALL_STATUS.json'))['modules']
F = json.loads(show(E+'prov-p1c-20261109/PCQC_FAILURES.json'))['failures']
fail_by_def = {f['gate_definition']: f for f in F if f.get('gate_definition')}
changed = {c['key']: c for c in C['changes']}
EXCL = ('NCV_', 'NCX_', 'NEG_PushActual', 'NGD_')   # PCWG_ owns NCV/NCX/NEG/NGD; PCWH_ the nine slice-iterator roots; PCWI_ op50
EXCL_MOD = {'Op50_Source', 'Op50'}                  # op50 (PCWI_); nine slice-iterator roots are listed in SLICE_ROOTS below if present
SLICE_ROOTS = set()  # filled from PCXH class listing of DEPENDS/slice roots if any; none identified as OPEN-class modules by name
out = []; excluded = collections.Counter(); subtracted = []
for k, v in P.items():
    if v != 'OPEN': continue
    m, n = k.split('|', 1)
    if m.startswith(EXCL) or 'Op50' in m or m in SLICE_ROOTS:
        excluded[m] += 1; continue
    if k in changed:
        subtracted.append({'key': k, 'now': changed[k]['now'], 'theorem': changed[k].get('theorem')}); continue
    r = U.get(m, {}).get(n) or {}
    base = r.get('base_status'); reason = (r.get('open_reason') or '')
    ev = 'evidence/prov-p2j-20261110/PCUJ_ALL_STATUS.json#modules/%s/%s (decided_by %s)' % (m, n, r.get('decided_by'))
    note = reason[:200].replace('\n', ' ')
    typeish = bool(re.search(r'Types|TypesV1|QuarticFieldSlice', m)) or 'inductive' in reason or 'struct' in reason.split('generator emits')[-1][:80]
    if reason.startswith(('missing_in_gate', 'external_instantiated')):
        cause = 'GATE_ONLY_HELPER'
    elif typeish and base in ('TEXT_IDENTICAL_ONLY', 'TEXT_ONLY_NOT_COMPARED', 'TEXT_DIFFERS', 'NO_COMMON_LEAN_NAME', 'FAILED', None, 'NO_FRESH_EMISSION', 'NOT_COVERED'):
        cause = 'TYPES'
    elif n in fail_by_def or any(n.startswith(g + '.') or n.startswith(g + '_') for g in fail_by_def):
        g = n if n in fail_by_def else [g for g in fail_by_def if n.startswith(g + '.') or n.startswith(g + '_')][0]
        cause = 'CANNOT_EXTRACT'; ev = 'evidence/prov-p1c-20261109/PCQC_FAILURES.json (%s: %s)' % (fail_by_def[g]['p1c_run'], fail_by_def[g]['error'][:120])
    elif base == 'FAILED' or 'FAILED' in reason or reason.startswith('OPEN_TWO_FAILED') or base == 'NOT_PROVED_P3':
        cause = 'COMPARE_FAILED'
    elif base in ('TEXT_IDENTICAL_ONLY', 'TEXT_ONLY_NOT_COMPARED', 'NO_COMMON_LEAN_NAME', 'TEXT_DIFFERS') or reason.startswith('TEXT_IDENTICAL_ONLY') or 'WRONG_BASIS' in reason:
        cause = 'EMITTED_NOT_COMPARED'
    else:
        cause = 'NO_FRESH_EMISSION'
    out.append({'module': m, 'definition': n, 'cause': cause, 'base_status': base, 'reason': note, 'evidence': ev})
tab = collections.defaultdict(collections.Counter)
for r in out: tab[r['module']][r['cause']] += 1
res = {'schema': 'PCWJ_TRIAGE/1', 'target_established': False,
       'baseline': 'PCXH_PROVENANCE.json per_definition_class OPEN (484) minus PCXJ_COUNTS.json changes (P2k, P3u, P3w, P3v, P3x credits) minus excluded sibling modules',
       'n_open_baseline': sum(1 for v in P.values() if v == 'OPEN'), 'n_subtracted_as_proved': len(subtracted), 'n_excluded_sibling': sum(excluded.values()),
       'excluded_modules': dict(excluded), 'subtracted': subtracted, 'n_triaged': len(out),
       'cause_totals': dict(collections.Counter(r['cause'] for r in out)),
       'per_module': {m: dict(c) for m, c in sorted(tab.items(), key=lambda x: -sum(x[1].values()))}, 'records': out}
d = sys.argv[1] if len(sys.argv) > 1 else '.'
json.dump(res, open(d + '/PCWJ_TRIAGE.json', 'w'), indent=1)
with open(d + '/PCWJ_TRIAGE_TABLE.md', 'w') as f:
    f.write('module | n | ' + ' | '.join(sorted(res['cause_totals'])) + '\n')
    for m, c in res['per_module'].items(): f.write('%s | %d | %s\n' % (m, sum(c.values()), ' | '.join(str(c.get(x, 0)) for x in sorted(res['cause_totals']))))
print(res['n_open_baseline'], res['n_subtracted_as_proved'], res['n_excluded_sibling'], res['n_triaged'], res['cause_totals'])
