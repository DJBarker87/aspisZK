#!/bin/bash
# PCXE_audit.sh: PCXE_AUDIT.json (scopes, axiom union, credited-theorem-by-name coverage) and PCXE_RENAMES.json (credited theorem name -> audited constant(s)).
cd /Users/dominic/ZK/.worktrees/pc-prov-p6t/evidence
python3 -I -B - <<'PY'
import json, re, lzma, os, collections
D = 'prov-p6t-20261110'; STD = {'propext', 'Classical.choice', 'Quot.sound'}
att = [json.loads(l) for l in open(f'{D}/PCXE_ATTEMPTS.jsonl')]
res = [e for e in att if e.get('event') == 'result']
def log(a):
    p = f'{D}/{a}/stdout.log'
    return open(p).read() if os.path.exists(p) else lzma.open(p + '.xz').read().decode()
scopes = []
for e in res:
    a = e['attempt']; rc = json.load(open(f'{D}/{a}/receipt.json')); t = log(a)
    scopes.append(dict(attempt=a, target=e['module'], exit=rc['exit_status'], wall_seconds=round(rc['wall_seconds'], 1), peak_rss_kib=int(rc['peak_rss_kib']), swaps=rc['swaps'], errors=len([l for l in t.split('\n') if ': error' in l]), source_revision=rc['source_revision'], source_tree_dirty=rc['source_tree_dirty'], source_sha256=list(rc['source_hashes'].values())[0]))
root = [s for s in scopes if s['target'] == 'PRVCmb_ROOT']
out = dict(schema='PCXE_AUDIT/1', target_established=False, scopes=scopes, n_lean_scopes_in_this_job=len(scopes),
           reused_unchanged_objects='PRVCmb_C01..C12 and PRVH_WrapAdd from the P6c workspace (PCXB_exports, byte-identical bundle sources), PRVCmb_C13 from the P6x workspace (PCXC_exports, corrected copy); recompiled here: C14..C17 and ROOT')
if root and root[-1]['exit'] == 0:
    a = root[-1]['attempt']; t = log(a)
    ax = {}
    for n, rest in re.findall(r"^'([^']+)' (does not depend on any axioms|depends on axioms: \[[^\]]*\])", t, re.M):
        ax[n] = [] if rest.startswith('does') else [x.strip() for x in rest[rest.index('[') + 1:-1].replace('\n', ' ').split(',')]
    kinds = dict(re.findall(r'^PRVEQ_KIND (\S+) (\S+)$', t, re.M))
    un = re.search(r'PRVCMB_UNION_AXIOMS \[([^\]]*)\] ms=(\d+)', t); cnt = re.search(r'PRVEQ_AUDIT_COUNT (\d+) skipped_by_time_guard=(\d+) ms=(\d+)', t); loc = re.search(r'PRVEQ_LOCAL_AXIOM_DECLS (\d+) (.*)', t)
    skipped = re.findall(r'^PRVCMB_PERITEM_SKIPPED_TIME_GUARD (\S+)', t, re.M)
    nonstd = {n: v for n, v in ax.items() if set(v) - STD}
    strip = lambda n: re.sub(r'(?<=PRVEq\.)C\d\d_F\d\d\.', '', re.sub(r'_C\d\d_F\d\d', '', n))
    norm = lambda n: re.sub(r'_(Funs|Types)(?=\.|$)', r'.\1', n)
    audited = collections.defaultdict(list)
    for n in kinds: audited[norm(strip(n))].append(n)
    q = json.load(open('prov-p6t-20261110/PCXE_ALL_STATUS.json'))['modules']
    cred = [(m, r['definition'], r['theorem']) for m, d in q.items() for r in d.values() if r['status'] in ('EQUALITY_PROVED', 'EQUALITY_DOMAIN', 'CONDITIONAL_ON_BINDING', 'DEPENDS_ON_LIBRARY_TRUST') and r.get('theorem')]
    # PCXE overlays: P3b V8R19 M31.mul (PCXE-C2); the three theorem names
    for m, n, th in [('AspisV8R19.ComplexFieldSlice', 'AspisR65Field.field.M31.mul', 'PRVEq.AspisV8R19.ComplexFieldSlice.field.M31.mul'), ('AspisV8R19.GuardedFieldSlice', 'AspisR64Field.field.M31.mul', 'PRVEq.AspisV8R19.GuardedFieldSlice.aspis_core.field.M31.mul'), ('AspisV8R19.QuarticFieldSlice', 'AspisR66Field.field.M31.mul', 'PRVEq.AspisV8R19.QuarticFieldSlice.field.M31.mul')]:
        cred = [c for c in cred if not (c[0] == m and c[1] == n)] + [(m, n, th)]
    def first(t): return t.split(' ;')[0].split(' (+')[0].strip()
    renames = []; miss = []
    for m, d, th in cred:
        t = norm(first(th)); hit = [(v, audited[v]) for v in (t, t + '.equiv') if v in audited]
        if hit: renames.append(dict(module=m, definition=d, credited_name=first(th), audited_constants=hit[0][1]))
        else: miss.append(dict(module=m, definition=d, theorem=th))
    json.dump(dict(schema='PCXE_RENAMES/1', rule='credited name = audited constant with the tag Ckk_Fjj removed (PCXB-C2/PCXE-C4), Funs/Types spelled with a dot, optional .equiv suffix', n=len(renames), records=renames), open(f'{D}/PCXE_RENAMES.json', 'w'))
    out.update(root_scope=a, union_axioms=un[1] if un else None, union_ms=int(un[2]) if un else None, audited_constants=len(kinds), audited_theorems_per_item=int(cnt[1]) if cnt else None, per_item_skipped_by_time_guard=int(cnt[2]) if cnt else None, skipped_names=skipped[:20],
               per_constant_nonstandard=nonstd, local_axiom_decls=(int(loc[1]), loc[2][:300]) if loc else None, kinds=dict(collections.Counter(kinds.values())),
               credited_theorem_records=len(cred), credited_theorem_names_found=len(cred) - len(miss), credited_not_found=miss[:200], n_not_found=len(miss), renames_file=f'{D}/PCXE_RENAMES.json')
json.dump(out, open(f'{D}/PCXE_AUDIT.json', 'w'), indent=1)
print({k: v for k, v in out.items() if k not in ('scopes', 'credited_not_found', 'skipped_names')})
PY
