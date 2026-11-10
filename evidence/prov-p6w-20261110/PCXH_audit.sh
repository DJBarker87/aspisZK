#!/bin/bash
# PCXH_audit.sh <root-attempt> [<audit-attempt>:<module> ...]  ->  PCXH_AUDIT.json and PCXH_RENAMES.json
# Reads the per-step stdout logs of the root scope (PRVCmb_L187_ROOT) and optional separate audit modules; credited names from PCXF_ALL_STATUS.json (git show, read-only).
cd "$(dirname "$0")"
ROOT="$1"; shift
PCXH_ROOT="$ROOT" PCXH_AUDS="$*" python3 -I -B - <<'PY'
import json, re, lzma, os, collections, subprocess
STD = {'propext', 'Classical.choice', 'Quot.sound'}
ROOT = os.environ['PCXH_ROOT']; AUDS = [x.split(':') for x in os.environ['PCXH_AUDS'].split() if x]
def show(p): return subprocess.check_output(['git', 'show', 'HEAD:' + p])
def log(a, mod):
    p = f'{a}/{mod}/stdout.log'
    return open(p).read() if os.path.exists(p) else lzma.open(p + '.xz').read().decode()
att = [json.loads(l) for l in open('PCXH_ATTEMPTS.jsonl')]
scopes = []
for e in att:
    if e.get('event') != 'result': continue
    for s in e['steps']:
        scopes.append(dict(attempt=e['attempt'], target=s['module'], exit=s['exit_status'], wall_seconds=round(s['wall_seconds'], 1), peak_rss_kib=int(s['peak_rss_kib']), swaps=s['swaps'], errors=s['errors'], scope_exit=e['exit_status'], source_revision=e['source_revision']))
def parse(t):
    ax = {}
    for n, rest in re.findall(r"^'([^']+)' (does not depend on any axioms|depends on axioms: \[[^\]]*\])", t, re.M):
        ax[n] = [] if rest.startswith('does') else [x.strip() for x in rest[rest.index('[') + 1:-1].replace('\n', ' ').split(',')]
    return ax
t = log(ROOT, 'PCXH_AUD_B'); ax = parse(t)
kinds = dict(re.findall(r'^PRVEQ_KIND (\S+) (\S+)$', t, re.M))
un = re.search(r'PRVCMB_UNION_AXIOMS \[([^\]]*)\] ms=(\d+)', t); cnt = re.search(r'PRVEQ_AUDIT_COUNT (\d+) skipped_by_time_guard=(\d+) ms=(\d+)', t); loc = re.search(r'PRVEQ_LOCAL_AXIOM_DECLS (\d+) (.*)', t)
skipped = re.findall(r'^PRVCMB_PERITEM_SKIPPED_TIME_GUARD (\S+)', t, re.M)
nonstd = {n: v for n, v in ax.items() if set(v) - STD}
strip = lambda n: re.sub(r'(?<=PRVEq\.)C\d\d_F\d\d\.', '', re.sub(r'_C\d\d_F\d\d', '', n))
norm = lambda n: re.sub(r'_(Funs|Types)(?=\.|$)', r'.\1', n)
audited = collections.defaultdict(list)
for n in kinds: audited[norm(strip(n))].append(n)
q = json.loads(show('evidence/prov-p6u-20261110/PCXF_ALL_STATUS.json'))['modules']
cred = [(m, r['definition'], r['theorem']) for m, d in q.items() for r in d.values() if r['status'] in ('EQUALITY_PROVED', 'EQUALITY_DOMAIN', 'CONDITIONAL_ON_BINDING', 'DEPENDS_ON_LIBRARY_TRUST') and r.get('theorem')]
for m, n, th in [('AspisV8R19.ComplexFieldSlice', 'AspisR65Field.field.M31.mul', 'PRVEq.AspisV8R19.ComplexFieldSlice.field.M31.mul'), ('AspisV8R19.GuardedFieldSlice', 'AspisR64Field.field.M31.mul', 'PRVEq.AspisV8R19.GuardedFieldSlice.aspis_core.field.M31.mul'), ('AspisV8R19.QuarticFieldSlice', 'AspisR66Field.field.M31.mul', 'PRVEq.AspisV8R19.QuarticFieldSlice.field.M31.mul')]:
    cred = [c for c in cred if not (c[0] == m and c[1] == n)] + [(m, n, th)]
def first(x): return x.split(' ;')[0].split(' (+')[0].strip()
renames = []; miss = []
for m, d, th in cred:
    nm = norm(first(th)); hit = [(v, audited[v]) for v in (nm, nm + '.equiv') if v in audited]
    if hit: renames.append(dict(module=m, definition=d, credited_name=first(th), audited_constants=hit[0][1]))
    else: miss.append(dict(module=m, definition=d, theorem=th))
json.dump(dict(schema='PCXH_CREDITED_NAMES/1', n=len(renames), records=renames), open('PCXH_CREDITED_NAMES.json', 'w'))
aud = []; allax = {}
for a, mod in AUDS:
    tt = log(a, mod); x = parse(tt); allax.update(x)
    tg = re.search(r'PRVCMB_AUDIT_TARGETS (.*) (\d+)$', tt, re.M); u2 = re.search(r'PRVCMB_UNION_AXIOMS \[([^\]]*)\]', tt); c2 = re.search(r'PRVEQ_AUDIT_COUNT (\d+) skipped_by_time_guard=(\d+)', tt)
    aud.append(dict(attempt=a, module=mod, audit_targets=int(tg[2]) if tg else None, per_item_audited=int(c2[1]) if c2 else None, skipped_by_time_guard=int(c2[2]) if c2 else None, union_axioms=u2[1] if u2 else None, nonstandard={k: sorted(set(v) - STD) for k, v in x.items() if set(v) - STD}, theorem_axiom_lines=len(x)))

_l = open('PCXH_audit_l.sh').read(); _e = _l[_l.index('EXP = {'):_l.index('\nres = []')]; _g = {}; exec(_e, _g); EXPD = _g['EXP']
dep = {}
for a, names in EXPD.items():
    f = {}; m = []
    for nm in names:
        h = [k for k in allax if k == nm or k.endswith('.' + nm)]
        (f.__setitem__(nm, h[0]) if h else m.append(nm))
    dep[a] = dict(n_expected=len(names), n_found=len(f), missing=m, found_as=f, nonstandard={k: sorted(set(allax[k]) - STD) for k in f.values() if set(allax[k]) - STD})
out = dict(schema='PCXH_AUDIT/1', target_established=False, universe='L187 replayed closure (final/objs, objs, base_ref); no ledger30 chain', scopes=scopes, n_lean_steps=len(scopes), root_scope=ROOT,
           union_axioms=un[1] if un else None, union_ms=int(un[2]) if un else None, audited_constants=len(kinds), audited_theorems_per_item=int(cnt[1]) if cnt else None, per_item_skipped_by_time_guard=int(cnt[2]) if cnt else None, skipped_names=skipped[:20],
           per_constant_nonstandard=nonstd, local_axiom_decls=(int(loc[1]), loc[2][:300]) if loc else None, kinds=dict(collections.Counter(kinds.values())),
           credited_theorem_records=len(cred), credited_theorem_names_found=len(cred) - len(miss), credited_not_found=miss[:300], n_not_found=len(miss), credited_names_file='PCXH_CREDITED_NAMES.json', renames_file='PCXH_RENAMES.json (declaration renames, separate)', separate_audit_modules=aud, deployed_body_names_in_root=dep, deployed_names_expected=sum(v['n_expected'] for v in dep.values()), deployed_names_found=sum(v['n_found'] for v in dep.values()))
json.dump(out, open('PCXH_AUDIT.json', 'w'), indent=1)
print({k: v for k, v in out.items() if k not in ('scopes', 'credited_not_found', 'skipped_names', 'separate_audit_modules')})
PY
