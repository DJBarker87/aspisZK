#!/bin/bash
# PCXB_nonfrozen.sh: detector for gate modules extracted from a source revision other than the frozen 4bb3b3f.
# For every Aeneas doc comment `[sym] Source: 'path', lines A:B-C:D` of every candidate text of every in-scope emitted module whose path exists in the frozen tree,
# check that the symbol's last identifier occurs in frozen lines A..C. A miss is a drift flag (detector limits recorded).
cd /Users/dominic/ZK/.worktrees/pc-prov-p6c/evidence/prov-p6c-20261109
python3 -I -B - <<'PY'
import sys, json, re, subprocess, collections
sys.path.insert(0, '.')
import PCXB_lib as L
FR = '4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
em = json.load(open(L.SCR + '/emods_decl.json')); c1 = json.load(open(L.SCR + '/compose1.json')); pco = L.J('prov-p0-20261109/PCO_PARTITION.json')['modules']
_cache = {}
def frozen(path):
    if path not in _cache:
        r = subprocess.run(['git', '-C', L.WT, 'show', f'{FR}:{path}'], capture_output=True)
        _cache[path] = r.stdout.decode('utf-8', 'replace').split('\n') if r.returncode == 0 else None
    return _cache[path]
DOC = re.compile(r"/--\s*\[([^\]]+)\]:?(.*?)-/", re.S)
res = {}; summary = collections.Counter()
for m in c1:
    flagged = []; checked = 0; skipped = collections.Counter()
    for s in em[m]['candidates']:
        t = L.blob_text(s)
        for dm in DOC.finditer(t):
            sym = dm[1].strip(); src = re.search(r"Source: '([^']+)', lines (\d+):\d+-(\d+):\d+", dm[2])
            if not src: skipped['no_source_line'] += 1; continue
            path, a, c = src[1], int(src[2]), int(src[3])
            if not path.startswith(('crates/', 'programs/')): skipped['not_frozen_tree_path'] += 1; continue
            fl = frozen(path)
            if fl is None: skipped['path_missing_in_frozen'] += 1; flagged.append(dict(symbol=sym, source=path, lines=f'{a}-{c}', problem='path absent from frozen tree', sha=s[:12])); continue
            last = re.sub(r'\{[^{}]*\}', '', sym).split('::')[-1].strip(' <>@')
            if not re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*', last) or last in ('closure', 'call', 'call_once', 'call_mut', 'body', 'clone', 'eq', 'fmt'): skipped['name_not_checkable'] += 1; continue
            checked += 1
            if c > len(fl): flagged.append(dict(symbol=sym, source=path, lines=f'{a}-{c}', problem='range beyond frozen file length', sha=s[:12])); continue
            txt = '\n'.join(fl[a - 1:c])
            if not re.search(r'\b' + re.escape(last) + r'\b', txt): flagged.append(dict(symbol=sym, source=path, lines=f'{a}-{c}', problem=f'identifier {last} not in frozen lines', sha=s[:12]))
    uniq = {(f['symbol'], f['source'], f['lines']): f for f in flagged}
    res[m] = dict(checked=checked, skipped=dict(skipped), flagged=list(uniq.values()), splitB=bool(c1[m]['splitB_names']), closed=bool(c1[m]['closed_names']), group=pco[m]['group'])
    summary['modules_with_flag' if uniq else 'modules_clean'] += 1
out = dict(schema='PCXB_NONFROZEN/1', target_established=False, frozen=FR, summary=dict(summary),
  detector='Aeneas doc-comment Source line ranges vs frozen file text at 4bb3b3f (identifier-in-range test)',
  detector_limits=['Only definitions with a Source: line in a crates/ or programs/ path are checked; library (/rustc/...) items, closures, trait-method names (clone/eq/fmt/call), loop/body helpers, generated names and hand-written definitions are skipped.',
     'An identifier-in-range hit does not prove the body equals the frozen body: a revision that moved a function by a few lines or kept its name but changed its body is not detected (e.g. the M31.mul fast path would be missed if its line range still contained `mul`); such cases are found only by the P2 equality passes.',
     'A flag shows the line range does not contain the identifier in the frozen file; it is evidence of a different revision or of renamed/wrapped source, not proof.'],
  modules={m: v for m, v in res.items() if v['flagged']}, modules_checked=len(res))
json.dump(out, open('PCXB_NONFROZEN_DETECT.json', 'w'), indent=1)
print(summary, [(m, len(v['flagged'])) for m, v in res.items() if v['flagged']][:40])
PY
