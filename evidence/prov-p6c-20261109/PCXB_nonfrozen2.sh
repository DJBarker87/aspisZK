#!/bin/bash
# PCXB_nonfrozen2.sh: PCXB_NONFROZEN.json. Detector (frozen-line-range identifier test, now also mapping bare `src/` Source paths to crates/<crate>/src/)
# plus revision identification: for each flagged (module, source file) find, among ALL distinct blobs of same-named files in the history of `research`,
# those where every flagged definition's doc-comment line range contains its identifier.
cd /Users/dominic/ZK/.worktrees/pc-prov-p6c/evidence/prov-p6c-20261109
python3 -I -B - <<'PY'
import sys, json, re, subprocess, collections, threading
sys.path.insert(0, '.')
import PCXB_lib as L
FR = '4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
em = json.load(open(L.SCR + '/emods_decl.json')); c1 = json.load(open(L.SCR + '/compose1.json')); pco = L.J('prov-p0-20261109/PCO_PARTITION.json')['modules']
def git(*a): return subprocess.run(['git', '-C', L.WT, *a], capture_output=True)
_c = {}
def frozen(path):
    if path not in _c:
        r = git('show', f'{FR}:{path}'); _c[path] = r.stdout.decode('utf-8', 'replace').split('\n') if r.returncode == 0 else None
    return _c[path]
DOC = re.compile(r"/--\s*\[([^\]]+)\]:?(.*?)-/", re.S)
SKIP = ('closure', 'call', 'call_once', 'call_mut', 'body', 'clone', 'eq', 'fmt')
def crate_dir(sym):
    first = sym.split('::')[0].strip().lstrip('<{')
    return {'aspis_core': 'crates/aspis-core', 'aspis_statement': 'crates/aspis-statement', 'aspis_r1_cost_probe': 'crates/aspis-r1-cost-probe', 'aspis_r1_cost_probe_program': 'programs/r1-cost-probe', 'aspis_pool': 'crates/aspis-pool'}.get(first)
per = {}   # module -> {srcpath: {(sym,a,c,last)}}
for m in c1:
    d = collections.defaultdict(set)
    for s in em[m]['candidates']:
        for dm in DOC.finditer(L.blob_text(s)):
            sym = dm[1].strip(); src = re.search(r"Source: '([^']+)', lines (\d+):\d+-(\d+):\d+", dm[2])
            if not src: continue
            last = re.sub(r'\{[^{}]*\}', '', sym).split('::')[-1].strip(' <>@')
            if not re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*', last) or last in SKIP: continue
            d[src[1]].add((sym, int(src[2]), int(src[3]), last))
    per[m] = d
flag = collections.defaultdict(lambda: collections.defaultdict(list)); skipped = collections.Counter(); checked = collections.Counter()
for m, d in per.items():
    for path, items in d.items():
        for sym, a, c, last in items:
            fp = path
            if path.startswith('src/'):
                cd = crate_dir(sym)
                if not cd: skipped['src_path_unmapped_crate'] += 1; continue
                fp = cd + '/' + path
            elif not path.startswith(('crates/', 'programs/')): skipped['library_or_other_path'] += 1; continue
            fl = frozen(fp); checked[m] += 1
            if fl is None: flag[m][path].append((sym, a, c, last, 'frozen path absent: ' + fp)); continue
            if c > len(fl) or not re.search(r'\b' + re.escape(last) + r'\b', '\n'.join(fl[a - 1:c])): flag[m][path].append((sym, a, c, last, 'identifier not in frozen range ' + fp))
# ---- blob index of history
need_base = {p.split('/')[-1] for m in flag for p in flag[m]}
blobs = collections.defaultdict(dict)   # basename -> blob -> (commit date, commit, path)
for base in need_base:
    r = git('log', 'research', '--format=%H %cs', '--name-only', '--diff-filter=AM', '--', '*' + base)
    cur = None
    for l in r.stdout.decode().split('\n'):
        if re.fullmatch(r'[0-9a-f]{40} \d{4}-\d\d-\d\d', l): cur = l.split()
        elif l.strip() and cur and l.endswith(base):
            o = git('rev-parse', f'{cur[0]}:{l}').stdout.decode().strip()
            if o and (o not in blobs[base] or cur[1] < blobs[base][o][0]): blobs[base][o] = (cur[1], cur[0], l)
texts = {}
def blob(o):
    if o not in texts: texts[o] = git('cat-file', '-p', o).stdout.decode('utf-8', 'replace').split('\n')
    return texts[o]
out = {}
for m in sorted(flag):
    ents = []
    for path, items in flag[m].items():
        base = path.split('/')[-1]; allitems = per[m][path]
        # identification uses every checkable definition of this module+file (flagged or not)
        match = []; scored = []
        for o, (dt, cm, p) in blobs[base].items():
            fl = blob(o); n_ok = 0
            for sym, a, c, last in allitems:
                if not (c > len(fl) or not re.search(r'\b' + re.escape(last) + r'\b', '\n'.join(fl[a - 1:c]))): n_ok += 1
            scored.append((n_ok, dt, cm[:11], p, o[:12]))
            if n_ok == len(allitems): match.append((dt, cm[:11], p, o[:12]))
        match.sort(); scored.sort(key=lambda x: (-x[0], x[1]))
        ents.append(dict(source_path=path, n_definitions_checked=len(allitems), differing_definitions=[dict(symbol=s, lines=f'{a}-{c}', problem=pr) for s, a, c, l, pr in items],
                         n_history_blobs=len(blobs[base]), n_blobs_matching_all_ranges=len(match), best_partial_matches_top3=[dict(matched=x[0], of=len(allitems), date=x[1], commit=x[2], path=x[3], blob=x[4]) for x in scored[:3]], matching_blobs_earliest=match[:3], matching_blobs_latest=match[-2:],
                         identification='UNIQUE_OR_FEW' if 0 < len(match) <= 3 else 'AMBIGUOUS_MANY' if match else 'NO_HISTORY_BLOB_MATCHES_ALL_RANGES'))
    out[m] = dict(group=pco[m]['group'], in_splitB_cone=bool(c1[m]['splitB_names']), in_CLOSED_root_cone=bool(c1[m]['closed_names']), files=ents)
json.dump(dict(schema='PCXB_NONFROZEN/1', target_established=False, frozen=FR, modules_scanned=len(c1), modules_flagged=len(out), skipped=dict(skipped),
  detector='Aeneas doc-comment Source line ranges vs frozen file text at 4bb3b3f (identifier-in-range test); bare `src/x.rs` paths mapped to crates/<crate>/src/x.rs by the symbol crate',
  detector_limits=['Only crates/ programs/ and bare src/ Source paths with a checkable identifier are tested; library (/rustc/...) items, closures, trait-method names, loop/body helpers and hand-written definitions are skipped.',
   'An identifier-in-range hit does not prove the body equals the frozen body (a same-named function moved to the same lines with a changed body is not detected).',
   'Revision identification matches doc-comment ranges only (no body comparison): matching blobs are candidates, listed earliest/latest by commit date; AMBIGUOUS_MANY means ranges alone do not select a revision.',
   'History searched: `git log research` additions/modifications of files with the same basename; files that existed only outside research history are not found.'],
  modules=out), open('PCXB_NONFROZEN.json', 'w'), indent=1)
print(len(out), 'flagged modules'); print([(m, [(f['source_path'], f['n_blobs_matching_all_ranges']) for f in v['files']]) for m, v in out.items()][:30])
PY
