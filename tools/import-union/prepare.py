#!/usr/bin/env python3
"""Pin the retained union's source graph and prepare a private host overlay.

Does not compile or edit any candidate. Requires a read-only host object census
(--host-objects); selected local objects are copied, never overwritten in place.
"""
import argparse
from collections import defaultdict
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[2]
BASE = ROOT / 'docs/research/100bit-spend-path-20261013'
E = BASE / 'evidence/import-union-20261022'
HOST = '/home/dombarker/project-offloads/codex-cx-import-union-20261022'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
def imports(p):
    return [m for line in re.findall(r'^\s*import\s+([^\n]+)', p.read_text(), re.M)
            for m in line.split('--')[0].split()]
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--host-objects', type=Path, required=True)
    ap.add_argument('--staging', type=Path, required=True)
    args = ap.parse_args()
    stage = args.staging
    stage.mkdir(parents=True, exist_ok=True)
    hostobjects = json.loads(args.host_objects.read_text())
    # The part-52 preflight expands the part-51 terminal-cone pin set.
    terminal = json.loads((BASE / 'evidence/prover-commit52-20261022/build/preflight-expanded.json').read_text())
    migration = json.loads((E / 'migration.json').read_text())
    tracked = subprocess.check_output(['git', 'ls-files', '*.lean'], cwd=ROOT, text=True).splitlines()
    files = [ROOT / p for p in tracked if p.startswith('docs/research/')]
    allnames = set(m for p in files for m in imports(p))
    def mod(p):
        suffix = p.as_posix().split('/lean/')[-1][:-5].replace('/', '.')
        if suffix in allnames:
            return suffix
        parts = p.with_suffix('').parts
        options = ['.'.join(parts[i:]) for i in range(len(parts)) if '.'.join(parts[i:]) in allnames]
        return max(options, key=len) if options else p.stem
    candidates = defaultdict(list)
    for p in files:
        candidates[mod(p)].append(p)
    def rank(p):
        s = str(p.relative_to(ROOT))
        return (0 if s.startswith('docs/research/100bit-spend-path-20261013/lean/') else
                1 if s.startswith('docs/research/v8-r0-zk-20261009/lean/') else
                2 if '/lean/' in s and '/evidence/' not in s else
                3 if '/lean-candidates/' in s else 4, s)
    selected = {m: min(ps, key=rank) for m, ps in candidates.items()}
    for m, rec in terminal['resolved_sources'].items():
        selected[m] = ROOT / rec['path']
    # Retained R22 groups use the tx1 extension, as pinned in the prior union.
    for kind in ['Types', 'Funs']:
        selected['AspisR1PublicPreparation.'+kind] = BASE / ('lean/bridge-tx1-e5c186ba3-20261016/AspisR1PublicPreparation/'+kind+'.lean')
    # Match the original row-cone source, not an evidence-only renamed copy.
    selected['AspisR1S3InactiveSource.Types'] = BASE / 'lean-candidates/s3-s9-current-repin-20261020/AspisR1S3InactiveSource/Types.lean'
    selected['AspisR1S3InactiveSource.Funs'] = BASE / 'lean-candidates/s3-s9-current-repin-20261020/AspisR1S3InactiveSource/Funs.lean'
    selected['R1SamplerByteWord'] = BASE / 'evidence/lean-sampler-byte-word-20261013/SamplerByteWord.source.lean'
    selected['ImportUnionAdapterChecks'] = E / 'AdapterChecks.lean'
    selected['RawUnionScan'] = ROOT / 'tools/import-union/RawUnionScan.lean'
    selected['ImportUnionReleaseGate'] = BASE / 'lean/ImportUnionReleaseGate.lean'
    # Cache precedence for the retained soundness endpoints (read-only).
    seed = json.loads((BASE / 'evidence/import-coll-20261021/ImportUnionHeadlineCx20261021-1/command.json').read_text())
    localpaths = [Path('/tmp/codex-cx-dv-twotx-20261021-objects')]
    frozen = json.loads((BASE / 'evidence/dv-twotx-20261021/OraclePortHeadlineFrozen2PerAttempt-1/command.json').read_text())
    localpaths += [Path(p) for p in frozen['lean_path'].split(':')]
    localpaths += [Path(p) for p in seed['lean_path'].split(':') if 'import-coll' not in p]
    localobjects = {}
    for root in dict.fromkeys(localpaths):
        if root.is_dir():
            for p in root.rglob('*.olean'):
                if not p.is_file():
                    continue
                localobjects.setdefault(str(p.relative_to(root))[:-6].replace('/', '.'), p)
    rawgraph = {r['module']: r for r in json.loads((BASE/'evidence/import-coll-20261021/raw-module-graph.json').read_text())}
    for m, r in rawgraph.items():
        p = Path(r['path'])
        if p.is_file():
            assert sha(p) == r['sha256'], m
            localobjects[m] = p
    (stage / 'local-cache-index.json').write_text(json.dumps({m:str(p) for m,p in localobjects.items() if m not in hostobjects},sort_keys=True))
    if (stage / 'raw-local-graph.json').is_file():
        rawgraph.update(json.loads((stage / 'raw-local-graph.json').read_text()))
    if (stage / 'raw-host-graph.json').is_file():
        rawgraph.update(json.loads((stage / 'raw-host-graph.json').read_text()))
    migrated_paths = {r['path'] for r in migration['files']}
    changed = {m for m,p in selected.items() if str(p.relative_to(ROOT)) in migrated_paths}
    # Reverse closure restricted to the selected retained environment. Archived
    # alternate providers are pinned by migration.json, not imported simultaneously.
    graph = {m: imports(p) for m, p in selected.items() if p.is_file()}
    cachegraph = {m:r['imports'] for m,r in rawgraph.items()}
    cachegraph.update(graph)
    affected = set(changed)
    while True:
        new = affected | {m for m, ds in cachegraph.items() if any(d in affected for d in ds)}
        if new == affected:
            break
        affected = new
    roots = ['ImportUnionNamedDiscriminant', 'ImportUnionAdapterChecks', 'ImportUnionReleaseGate']
    # Every distinct migrated generated module gets a focused check, including
    # otherwise archived types, after the retained release closure is established.
    extra = sorted(m for m in changed if m in selected and '/evidence/' not in str(selected[m]))
    ordered, done, active, reused, cachepins = [], set(), set(), {}, []
    excluded = {'Init','Lean','Std','Mathlib','Batteries','Aeneas','AeneasMeta','Aesop','Qq','Plausible','ProofWidgets','ImportGraph','LeanSearchClient','Lake'}
    def visit(m):
        if m in done:
            return
        if m in active:
            raise RuntimeError('cycle '+m)
        # Library modules are pinned by env J, never cold-built.
        lib = m.split('.')[0] in excluded
        must = m in affected or m in roots
        if not must and m in hostobjects:
            reused[m] = {'kind':'host-cache', 'path':hostobjects[m]}
            done.add(m)
            return
        if not must and m in localobjects:
            p = localobjects[m]
            dest = stage / 'retained-objects' / (m.replace('.', '/')+'.olean')
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(p, dest)
            rec = {'module':m,'path':str(p),'sha256':sha(p),'bytes':p.stat().st_size}
            cachepins.append(rec)
            reused[m] = {'kind':'retained-local-cache', **rec}
            # Source graph and prior raw-object census provide direct imports.
            ds = rawgraph[m]['imports'] if m in rawgraph else graph.get(m)
            if ds is None:
                ds = next((r['imports'] for r in json.loads((BASE/'evidence/import-coll-20261021/raw-module-graph.json').read_text()) if r['module']==m), None)
            if ds is None:
                raise RuntimeError('missing import graph for retained object '+m)
            active.add(m)
            for d in ds:
                visit(d)
            active.remove(m)
            done.add(m)
            return
        if lib:
            raise RuntimeError('missing pinned library '+m)
        p = selected.get(m)
        if p is None or not p.is_file():
            raise RuntimeError('missing selected source '+m+' affected='+str(m in affected)+' selected='+str(p))
        active.add(m)
        for d in graph[m]:
            visit(d)
        dest = stage / 'sources' / (m.replace('.', '/')+'.lean')
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(p, dest)
        ordered.append({'module':m,'path':str(p.relative_to(ROOT)), 'sha256':sha(p), 'imports':graph[m], 'affected':m in affected})
        done.add(m)
        active.remove(m)
    for m in roots:
        visit(m)
    for m in extra:
        visit(m)
    roots.append('RawUnionScan')
    visit('RawUnionScan')
    # Explicitly retain top-level terminal targets via the release union imports.
    plan = {'revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
            'targets':roots+extra,'ordered':ordered,'reused':reused,'cache_pins':cachepins,
            'changed_modules':sorted(changed),'affected_in_selected_union':sorted(set(r['module'] for r in ordered)&affected),
            'terminal_preflight_sha256':sha(BASE/'evidence/prover-commit52-20261022/build/preflight-expanded.json'),
            'environment':{},'lean_paths':[HOST+'/retained-objects','/home/dombarker/project-offloads/aspis-joint-20261019/objects']}
    (stage / 'plan-local.json').write_text(json.dumps(plan,indent=2,sort_keys=True)+'\n')
    print('ordered',len(ordered),'retained objects',len(cachepins),'host cache roots',sum(r['kind']=='host-cache' for r in reused.values()))
if __name__ == '__main__':
    main()
