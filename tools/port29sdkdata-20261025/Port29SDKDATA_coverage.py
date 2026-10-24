#!/usr/bin/env python3
"""Target coverage supplement using the already pinned graph; no compiler."""
import collections
import hashlib
import json
from pathlib import Path
import resource
import subprocess
import sys
import time

start = time.monotonic()
R = Path(__file__).resolve().parents[2]
E = R / 'evidence/port29sdkdata-20261025'
audit = json.loads((E / 'Port29SDKDATA_audit.json').read_text())
graph_pin = next(x for x in audit['retained_outputs'] if x['path'].endswith('cross-origin-edges.jsonl'))
graph_path = Path(graph_pin['path'])
h = hashlib.sha256()
with graph_path.open('rb') as f:
    for b in iter(lambda: f.read(1024*1024), b''):
        h.update(b)
assert h.hexdigest() == graph_pin['sha256'] and graph_path.stat().st_size == graph_pin['bytes']
original = set()
current = set()
factor = set()
graph = collections.defaultdict(set)
with graph_path.open() as f:
    for line in f:
        row = json.loads(line)
        if row['side'] == 'ORIGINAL':
            original.add(row['name'])
        else:
            current.add(row['name'])
            if row['module'] == 'S6SdkDependencyFactorV1':
                factor.add(row['name'])
        graph[row['name']].update(row['dependencies'])
work_pin = next(x for x in audit['retained_outputs'] if x['path'].endswith('union-worklist.json'))
work_bytes = Path(work_pin['path']).read_bytes()
assert hashlib.sha256(work_bytes).hexdigest() == work_pin['sha256']
work = json.loads(work_bytes)
root_seeds_path = Path('/private/tmp/port28rootexport-20261024-2e053459f91b43c3b4c640d575d607c9/seeds.tsv')
root_seeds = {l.split('\t')[1] for l in root_seeds_path.read_text().splitlines()}
aux = 'AspisR1.S2W_D189Wrappers.reserve._unsafe_rec'
seeds = set(work['seeds']) - {aux}
seen = set()
pending = list(seeds)
while pending:
    n = pending.pop()
    if n in seen:
        continue
    seen.add(n)
    pending.extend(graph[n] - seen)
data = dict(schema='Port29SDKDATA-target-coverage-v1',
    command=[sys.executable, '-B', str(Path(__file__).resolve())],
    source_revision=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=R, text=True).strip(),
    tool_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(), graph_input=graph_pin, worklist_input=work_pin,
    root_seeds_total=len(root_seeds), root_seeds_in_current=len(root_seeds & current),
    root_seeds_missing_current=sorted(root_seeds-current),
    current_factor_selected_names=len(factor), current_factor_names_in_original_selected=len(factor & original),
    current_factor_names_missing_original_selected=sorted(factor-original),
    auxiliary_excluded_candidate=dict(seeds=len(seeds), reachable=len(seen), auxiliary_still_reachable=aux in seen,
        raw_missing=sorted(seen-original-current),
        status='Graph-only candidate, not safe logical closure; full metadata/project-axiom audit and reconstruction pending'),
    declaration_pairs='1059 name pairs pending full ConstantInfo comparison; missing counterpart never classified equal',
    newer_cut_transport='All six newer enclosing cut/equivalence/consumer modules absent from this released raw payload',
    print_axioms='N/A: noncompiler graph audit', lean_invocations=0,
    exit_status=0, wall_seconds=time.monotonic()-start, peak_rss_bytes=resource.getrusage(0).ru_maxrss,
    swaps=resource.getrusage(0).ru_nswap,
    runtime=dict(version=sys.version, executable=sys.executable,
        executable_sha256=hashlib.sha256(Path(sys.executable).resolve().read_bytes()).hexdigest()))
with (E / 'Port29SDKDATA_coverage.json').open('x') as f:
    json.dump(data, f, indent=2)
    f.write('\n')
print(json.dumps({k:data[k] for k in ['root_seeds_in_current','root_seeds_missing_current','current_factor_selected_names',
    'current_factor_names_missing_original_selected','wall_seconds','peak_rss_bytes']}))
