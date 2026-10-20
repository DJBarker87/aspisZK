# joint-manifest.py --repo <repo checkout> --roots M1,M2,... --out manifest.json [--libpath DIR:DIR...] [--check]
#
# One source per module name, from ONE repo revision (DESIGN-BUILD-INTEGRATION §3, LOG D63.2).
# Source roots, in priority order (a module name found in several roots with DIFFERENT bytes is
# taken from the earliest root and reported under "conflicts"; identical bytes are not a conflict):
ROOTS = [
  ('spend',    'docs/research/100bit-spend-path-20261013/lean', True),   # True: R1<File> alias
  ('base',     'AspisFormal', False),
  ('base',     'docs/research/v8-wide-reference-20261005/lean', False),
  ('base',     'docs/research/v8-fs-generic-20261006/lean', False),
  ('base',     'docs/research/v8-r0-close-20261007/lean', False),
  ('base',     'docs/research/v8-r0-fs-20261006/lean', False),
  ('base',     'docs/research/v8-r0-sem-20261007/lean', False),
  ('base',     'docs/research/v8-r0-sem-proof-20261008/lean', False),
  ('base',     'docs/research/v8-full-view-zk-20260912/lean', False),
  ('base',     'docs/research/v8-audit-20261005/lean', False),
  ('privacy',  'docs/research/v8-r1-20261011/lean', False),
  ('privacy',  'docs/research/v8-r0-zk-20261009/lean', False),
]
# Explicit current source owners; older split/extraction copies remain archival.
CANONICAL_SOURCES = {'R1FunctionalBatchClean': 'docs/research/100bit-spend-path-20261013/lean/R1FunctionalBatchClean.lean', 'R1SubfieldBatchStage2': 'docs/research/100bit-spend-path-20261013/lean/R1SubfieldBatchStage2.lean', 'SpendRelation': 'docs/research/100bit-spend-path-20261013/lean/SpendRelation.lean', 'SpendAppendBinding': 'docs/research/100bit-spend-path-20261013/lean/SpendAppendBinding.lean', 'TraceAppend': 'docs/research/100bit-spend-path-20261013/lean/TraceAppend.lean', 'R1SpendRelation': 'docs/research/100bit-spend-path-20261013/lean/R1SpendRelation.lean', 'R1SpendAppendBinding': 'docs/research/100bit-spend-path-20261013/lean/R1SpendAppendBinding.lean', 'R1TraceAppend': 'docs/research/100bit-spend-path-20261013/lean/R1TraceAppend.lean', 'SelectedTranscriptParams': 'docs/research/100bit-spend-path-20261013/lean/SelectedTranscriptParams.lean', 'UnifiedSampler': 'docs/research/100bit-spend-path-20261013/lean/UnifiedSampler.lean', 'SelectedChallengeMap': 'docs/research/100bit-spend-path-20261013/lean/SelectedChallengeMap.lean', 'R1SelectedTranscriptParams': 'docs/research/100bit-spend-path-20261013/lean/R1SelectedTranscriptParams.lean', 'R1UnifiedSampler': 'docs/research/100bit-spend-path-20261013/lean/R1UnifiedSampler.lean', 'R1SelectedChallengeMap': 'docs/research/100bit-spend-path-20261013/lean/R1SelectedChallengeMap.lean', 'R1UnifiedSamplerPublic': 'docs/research/100bit-spend-path-20261013/lean/R1UnifiedSamplerPublic.lean', 'R1SelectedChallengeMapCore': 'docs/research/100bit-spend-path-20261013/lean/R1SelectedChallengeMapCore.lean', 'AspisR1PublicPreparation.Funs': 'docs/research/100bit-spend-path-20261013/lean/extracted-public-preparation-c16-20261019/AspisR1PublicPreparation/Funs.lean', 'AspisR1PublicPreparation.Types': 'docs/research/100bit-spend-path-20261013/lean/extracted-public-preparation-c16-20261019/AspisR1PublicPreparation/Types.lean'}
CANONICAL_SOURCES.update({m: 'docs/research/100bit-spend-path-20261013/lean/bridge-selected-current-20261018/accepted-current/' + m.replace('.', '/') + '.lean' for m in ['AspisFormal.V6PublishedTheoremInterfaces', 'R0P.LogUpChain', 'R0P.LogUpAssembly', 'R0P.SemRounds']})

CANONICAL_SOURCES.update({m: 'docs/research/100bit-spend-path-20261013/lean/' + p for m,p in {'AspisR1PrefixAggregateParser.Types': 'bridge-prefix-aggregate-20261016/AspisR1PrefixAggregateParser/Types.lean', 'AspisR1TerminalDecoder.Types': 'bridge-decoder-public-20261016/AspisR1TerminalDecoder/Types.lean', 'AspisR1AdapterReconstruct.Types': 'bridge-adapter-public-20261016/AspisR1AdapterReconstruct/Types.lean'}.items()})
EXCLUDE_PREFIX = ('R1Mirror.',)          # the mirror leaves the build (§4 (a))
LIB = ('Mathlib', 'Batteries', 'Aesop', 'Qq', 'Lean', 'Init', 'Std', 'Plausible', 'ProofWidgets',
       'ImportGraph', 'LeanSearchClient', 'Lake', 'Cli', 'Aeneas', 'AeneasMeta')
# Library modules (Mathlib and friends from the AspisFormal consolidation packages; Aeneas and
# AeneasMeta from the 4.32 port backend) are prebuilt and read-only; --libpath checks they exist.
#
# --check: every module in the closure resolves to exactly one source (or a library object); no
# excluded module; no import cycle; no file imported under two module names (alias collision);
# writes nothing.  Without --check: writes the manifest (topological order, deps first).
import sys, os, re, json, hashlib, subprocess, argparse
ap = argparse.ArgumentParser()
ap.add_argument('--require-complete', action='store_true'); ap.add_argument('--repo', required=True); ap.add_argument('--roots', required=True)
ap.add_argument('--out'); ap.add_argument('--libpath', default=''); ap.add_argument('--check', action='store_true')
a = ap.parse_args()
def sha(p): return hashlib.sha256(open(p, 'rb').read()).hexdigest()
tracked = set(subprocess.run(['git', '-C', a.repo, 'ls-files', '*.lean'], capture_output=True,
                             text=True, check=True).stdout.split())
rev = subprocess.run(['git', '-C', a.repo, 'rev-parse', 'HEAD'], capture_output=True, text=True).stdout.strip()
dirty = subprocess.run(['git', '-C', a.repo, 'status', '--porcelain', '--untracked-files=no'],
                       capture_output=True, text=True).stdout.strip() != ''
index = {}                                   # module -> list of (kind, root, relpath, sha)
for kind, root, alias in ROOTS:
    for rel in sorted(p for p in tracked if p.startswith(root + '/')):
        sub = rel[len(root) + 1:]
        if '/evidence/' in '/' + sub or not sub.endswith('.lean'): continue
        parts = sub[:-5].split('/')
        cut = max([i + 1 for i, c in enumerate(parts) if '-' in c] or [0])
        mparts = parts[cut:]
        if not mparts or any(not re.match(r'^[A-Za-z_][A-Za-z0-9_]*$', c) for c in mparts): continue
        names = ['.'.join(mparts)]
        if alias and cut == 0 and len(mparts) == 1 and not mparts[0].startswith('R1'):
            names.append('R1' + mparts[0])
        h = sha(os.path.join(a.repo, rel))
        for n in names:
            if n in CANONICAL_SOURCES and rel != CANONICAL_SOURCES[n]: continue
            index.setdefault(n, []).append((kind, root, rel, h))
def imports_of(path):
    out = []
    for line in open(path, encoding='utf-8'):
        m = re.match(r'^(?:public\s+)?import\s+(.+)$', line.rstrip())
        if m: out += [x for x in m.group(1).split() if re.match(r'^[A-Z][A-Za-z0-9_.]*$', x)]
    return out
libdirs = [d for d in a.libpath.split(':') if d]
mods, libs, problems, conflicts = {}, {}, [], {}
todo = [r for r in a.roots.split(',') if r]
while todo:
    m = todo.pop()
    if m in mods or m in libs: continue
    if m.split('.')[0] in LIB:
        hit = next((os.path.join(d, m.replace('.', '/') + '.olean') for d in libdirs
                    if os.path.exists(os.path.join(d, m.replace('.', '/') + '.olean'))), None)
        libs[m] = hit
        if libdirs and not hit: problems.append(('library-missing', m))
        continue
    if m.startswith(EXCLUDE_PREFIX): problems.append(('excluded', m)); continue
    cands = index.get(m)
    if not cands: problems.append(('unresolved', m)); mods[m] = None; continue
    if len({c[3] for c in cands}) > 1:
        conflicts[m] = [{'kind': k, 'path': r, 'sha256': h} for k, _, r, h in cands]
    kind, root, rel, h = cands[0]
    imps = imports_of(os.path.join(a.repo, rel))
    mods[m] = {'kind': kind, 'source': rel, 'sha256': h, 'imports': imps}
    todo += imps
# alias collision: one file under two module names in the closure
byfile = {}
for m, v in mods.items():
    if v: byfile.setdefault(v['source'], []).append(m)
for f, ms in byfile.items():
    if len(ms) > 1: problems.append(('one-file-two-modules', f, sorted(ms)))
# topological order
order, state = [], {}
def visit(m, stack):
    if state.get(m) == 2 or m not in mods or not mods[m]: return
    if state.get(m) == 1: problems.append(('cycle', stack + [m])); return
    state[m] = 1
    for x in mods[m]['imports']: visit(x, stack + [m])
    state[m] = 2; order.append(m)
for m in sorted(mods): visit(m, [])
whole = sorted(m for m, v in mods.items() if v and 'Mathlib' in v['imports'])
rep = {'repo_revision': rev, 'repo_dirty': dirty, 'roots': a.roots.split(','),
       'module_count': len(order), 'library_count': len(libs),
       'kinds': {k: sum(1 for m in order if mods[m]['kind'] == k) for k in ('spend', 'base', 'privacy')},
       'problems': problems, 'conflicts': conflicts, 'imports_all_of_Mathlib': whole}
print(json.dumps({k: v for k, v in rep.items() if k != 'conflicts'} | {'conflict_count': len(conflicts)}, indent=1))
if a.check:
    sys.exit(1 if problems or conflicts else 0)
rep['order'] = [{'module': m, **mods[m]} for m in order]
rep['libraries'] = libs
json.dump(rep, open(a.out, 'w'), indent=1)

if a.require_complete and (problems or conflicts): sys.exit(2)
