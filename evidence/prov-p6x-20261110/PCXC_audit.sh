#!/bin/bash
# PCXC_audit.sh: PCXC_AUDIT.json from the bundle scopes and the root audit scope.
cd /Users/dominic/ZK/.worktrees/pc-prov-p6x/evidence
python3 -I -B - <<'PY'
import json, re, lzma, os, collections
D = 'prov-p6x-20261110'; STD = {'propext', 'Classical.choice', 'Quot.sound'}
att = [json.loads(l) for l in open(f'{D}/PCXC_ATTEMPTS.jsonl')]
res = [e for e in att if e['event'] == 'result']
def log(a):
    p = f'{D}/{a}/stdout.log'
    return open(p).read() if os.path.exists(p) else lzma.open(p + '.xz').read().decode()
scopes = []
for e in res:
    a = e['attempt']; rc = json.load(open(f'{D}/{a}/receipt.json')); t = log(a)
    scopes.append(dict(attempt=a, target=e['module'], exit=rc['exit_status'], wall_seconds=round(rc['wall_seconds'], 1), peak_rss_kib=int(rc['peak_rss_kib']), swaps=rc['swaps'], errors=len([l for l in t.split('\n') if ': error' in l]), source_revision=rc['source_revision'], source_tree_dirty=rc['source_tree_dirty'], source_sha256=list(rc['source_hashes'].values())[0]))
root = [s for s in scopes if s['target'] == 'PRVCmb_ROOT']
out = dict(schema='PCXC_AUDIT/1', target_established=False, scopes=scopes, n_lean_scopes=len(scopes))
if root and root[-1]['exit'] == 0:
    a = root[-1]['attempt']; t = log(a)
    ax = {}
    for n, rest in re.findall(r"^'([^']+)' (does not depend on any axioms|depends on axioms: \[[^\]]*\])", t, re.M):
        ax[n] = [] if rest.startswith('does') else [x.strip() for x in rest[rest.index('[') + 1:-1].replace('\n', ' ').split(',')]
    kinds = dict(re.findall(r'^PRVEQ_KIND (\S+) (\S+)$', t, re.M))
    un = re.search(r'PRVCMB_UNION_AXIOMS \[([^\]]*)\] ms=(\d+)', t); cnt = re.search(r'PRVEQ_AUDIT_COUNT (\d+) skipped_by_time_guard=(\d+) ms=(\d+)', t); loc = re.search(r'PRVEQ_LOCAL_AXIOM_DECLS (\d+) (.*)', t)
    skipped = re.findall(r'^PRVCMB_PERITEM_SKIPPED_TIME_GUARD (\S+)', t, re.M)
    nonstd = {n: v for n, v in ax.items() if set(v) - STD}
    # credited theorem names (PCQH records) covered, tag-insensitive
    strip = lambda n: re.sub(r'(?<=PRVEq\.)C\d\d_F\d\d\.', '', re.sub(r'_C\d\d_F\d\d', '', n))
    norm = lambda n: re.sub(r'_(Funs|Types)(?=\.|$)', r'.\1', n)
    audited = {norm(strip(n)) for n in kinds}
    q = json.load(open('prov-p1h-20261109/PCQH_ALL_STATUS.json'))['modules']
    cred = [(m, r['definition'], r['theorem']) for m, d in q.items() for r in d.values() if r['status'] in ('EQUALITY_PROVED', 'EQUALITY_DOMAIN', 'CONDITIONAL_ON_BINDING') and r.get('theorem')]
    def first(t): return t.split(' ;')[0].split(' (+')[0].strip()
    def found(t):
        t = norm(first(t)); return any(v in audited for v in (t, t + '.equiv'))
    miss = [c for c in cred if not found(c[2])]
    out.update(root_scope=a, union_axioms=un[1] if un else None, union_ms=int(un[2]) if un else None, audited_constants=len(kinds), audited_theorems_per_item=int(cnt[1]) if cnt else None, per_item_skipped_by_time_guard=int(cnt[2]) if cnt else None, skipped_names=skipped[:20],
               per_constant_nonstandard=nonstd, local_axiom_decls=(int(loc[1]), loc[2][:300]) if loc else None, kinds=dict(collections.Counter(kinds.values())),
               credited_theorem_records=len(cred), credited_theorem_names_found=len(cred) - len(miss), credited_not_found=[dict(module=c[0], definition=c[1], theorem=c[2]) for c in miss][:200], n_not_found=len(miss))
json.dump(out, open(f'{D}/PCXC_AUDIT.json', 'w'), indent=1)
print({k: v for k, v in out.items() if k not in ('scopes', 'credited_not_found', 'skipped_names')})
PY
