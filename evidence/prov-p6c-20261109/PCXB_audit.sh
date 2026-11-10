#!/bin/bash
# PCXB_audit.sh: aggregate the per-scope audit output into PCXB_AUDIT.json
cd /Users/dominic/ZK/.worktrees/pc-prov-p6c/evidence
python3 -I -B - <<'PY'
import json, re, lzma, glob, collections, os
D = 'prov-p6c-20261109'
STD = {'propext', 'Classical.choice', 'Quot.sound'}
scopes = {'PCXB_L001': 'A1', 'PCXB_L002': 'A2', 'PCXB_L003': 'A3', 'PCXB_L004': 'A4', 'PCXB_L005': 'A5', 'PCXB_L006': 'A6', 'PCXB_L007': 'A7', 'PCXB_L008': 'A8',
          'PCXB_L009': 'A9', 'PCXB_L010': 'A10', 'PCXB_L011': 'A11', 'PCXB_L012': 'A12'}
def log(a):
    p = f'{D}/{a}/stdout.log'
    return open(p).read() if os.path.exists(p) else lzma.open(p + '.xz').read().decode()
res = {}; allthm = {}
for a, b in scopes.items():
    t = log(a); rc = json.load(open(f'{D}/{a}/receipt.json'))
    errs = [l for l in t.split('\n') if ': error:' in l]
    kinds = dict(re.findall(r'^PRVEQ_KIND (\S+) (\S+)$', t, re.M))
    ax = {}
    for n, rest in re.findall(r"^'([^']+)' (does not depend on any axioms|depends on axioms: \[[^\]]*\])", t, re.M):
        ax[n] = [] if rest.startswith('does') else [x.strip() for x in rest[rest.index('[') + 1:-1].replace('\n', ' ').split(',')]
    nonstd = {n: v for n, v in ax.items() if set(v) - STD}
    cnt = re.search(r'PRVEQ_AUDIT_COUNT (\d+)', t); loc = re.search(r'PRVEQ_LOCAL_AXIOM_DECLS (\d+) (.*)', t)
    sorry = [n for n, v in ax.items() if 'sorryAx' in v]
    res[a] = dict(bundle='PRVEq_bundle_' + b, exit=rc['exit_status'], wall_seconds=round(rc['wall_seconds'], 1), peak_rss_kib=int(rc['peak_rss_kib']), swaps=rc['swaps'],
                  source_revision=rc['source_revision'], dirty=rc['source_tree_dirty'], bundle_sha256=list(rc['source_hashes'].values())[0], audit_count=int(cnt[1]) if cnt else None,
                  kinds=dict(collections.Counter(kinds.values())), errors=len(errs), first_errors=errs[:3], nonstandard=nonstd, sorryAx=sorry,
                  local_axiom_decls=(int(loc[1]), loc[2][:200]) if loc else None, cgroup_peak=rc.get('cgroup_memory_peak_bytes'))
    if rc['exit_status'] == 0:
        for n, v in ax.items(): allthm.setdefault(n, []).append((b, kinds.get(n), v))
ok = [a for a, r in res.items() if r['exit'] == 0 and r['errors'] == 0 and not r['nonstandard'] and not r['sorryAx']]
# credited theorems (PCUF_ALL_STATUS, correct basis, PROVED*) covered by the audit
st = json.load(open('prov-p2f-20261109/PCUF_ALL_STATUS.json'))['modules']
cred = [(r['module'], r['definition'], r['theorem'], r['status']) for m in st.values() for r in m.values() if r['status'].startswith('PROVED') and not r['basis_not_correct']]
named = [c for c in cred if c[2]]
def first(t): return t.split(' ;')[0].split(' (+')[0].strip()
import re as _re
def variants(t):
    t = first(t); v = [t, t + '.equiv']
    m = _re.match(r'PRVEq\.([A-Za-z0-9_]+?)_(Funs|Types)\.(.*)', t)
    if m: v += ['PRVEq.%s.%s.%s' % m.groups(), 'PRVEq.%s.%s.%s.equiv' % m.groups()]
    return v
def found(t): return any(x in allthm for x in variants(t))
covered = [c for c in named if found(c[2])]
missing = [c for c in named if not found(c[2])]
out = dict(schema='PCXB_AUDIT/1', target_established=False, scopes=res, scopes_ok_for_audit=ok,
           failed_scopes=[dict(scope=a, reason='bundle A6 compile error (S8OwnedP6 from_residual in bundle context); retired shape; replaced by PCXB_L011 (file alone) + PCXB_L012 (rest)') for a, r in res.items() if a not in ok],
           distinct_audited_names=len(allthm), names_with_nonstandard_axioms=[n for n, l in allthm.items() if any(set(x[2]) - STD for x in l)],
           credited_definitions=len(cred), credited_with_theorem_name=len(named), credited_theorem_names_covered=len(covered),
           credited_theorem_names_not_found_in_audit=[dict(module=c[0], definition=c[1], theorem=c[2]) for c in missing][:200], n_not_found=len(missing),
           same_name_in_more_than_one_scope=sorted(n for n, l in allthm.items() if len(l) > 1)[:50],
           collision_rule='PCXB-C1: files declaring a common fully-qualified name are in different bundles; no renaming. Names declared by prov-p2a NativeFunsQ415/p2f RPz7_FIo_NativeFuns, p2f/p3a RPu_FIq_Native08, p2f/p4a S8OwnedP6_Funs.',
           limits='Axiom audit by Lean.collectAxioms over every non-internal PRVEq.* constant of each bundle; compile environment is the ledger30 gate export; each bundle is a separate environment (no single combined environment).')
json.dump(out, open(D + '/PCXB_AUDIT.json', 'w'), indent=1)
print(json.dumps({k: out[k] for k in ['scopes_ok_for_audit', 'distinct_audited_names', 'credited_definitions', 'credited_with_theorem_name', 'credited_theorem_names_covered', 'n_not_found', 'names_with_nonstandard_axioms']}))
for a, r in res.items(): print(a, r['bundle'], r['exit'], r['audit_count'], r['errors'], len(r['nonstandard']), r['wall_seconds'], r['peak_rss_kib'])
print(out['credited_theorem_names_not_found_in_audit'][:5])
PY
