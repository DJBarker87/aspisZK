#!/usr/bin/env python3
"""Audit existing receipts and pin final direct imports; never invokes Lean."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
SRC = ROOT / 'docs/research/v8-r0-zk-20261009/lean'
PACKET = ROOT / 'docs/research/100bit-spend-path-20261013/evidence/priv-premises-20261020'
BASE = 'f3a8c44cf42463bdb947e6410caf0b571803940c'
HOST = 'dombarker@100.108.41.90'
J = '/home/dombarker/project-offloads/aspis-joint-20261019'
H = '/home/dombarker/project-offloads/r1-privacy-build-integration-20261019'

def sha(data):
    return hashlib.sha256(data).hexdigest()

def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT)

records = [json.loads(s) for s in (HERE / 'attempts.jsonl').read_text().splitlines()]
latest = {}
for rec in records:
    assert 6320 <= rec['attempt'] < 6400
    latest[rec['module']] = rec
for mod, rec in latest.items():
    assert rec['exit'] == 0, (mod, rec['exit'])
    source = SRC / (mod.replace('.', '/') + '.lean')
    assert sha(source.read_bytes()) == rec['source_sha256'], mod
    assert rec['swaps'] == '0'
    assert rec['axioms'] and not rec['errors']
    for line in rec['axioms']:
        ax = re.search(r'\[(.*)\]', line)
        if ax:
            assert set(ax.group(1).split(', ')) <= {'propext', 'Classical.choice', 'Quot.sound'}
    for theorem in re.findall(r'^theorem (\w+)', source.read_text(), re.M):
        assert any('.' + theorem + "'" in line for line in rec['axioms']), theorem

remote_script = '''import pathlib, hashlib, json, re
J=pathlib.Path(JJ); H=pathlib.Path(HH)
def pin(p):
 return dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size=p.stat().st_size)
result={}
for mod in MODULES:
 src=J/'sources'/(mod.replace('.','/')+'.lean')
 imports=re.findall(r'^import (\\S+)',src.read_text(),re.M)
 pins={m:pin(J/'objects'/(m.replace('.','/')+'.olean')) for m in sorted(imports)}
 fp=hashlib.sha256(';'.join(m+'='+p['sha256'] for m,p in pins.items()).encode()).hexdigest()[:16]
 result[mod]=dict(source=pin(src),direct_imports=pins,deps_fingerprint=fp,object=pin(J/'objects'/(mod.replace('.','/')+'.olean')))
print(json.dumps(dict(modules=result,environment=json.loads((H/'env/J.json').read_text()),launcher=pin(H/'tools/run-joint.sh'),driver=pin(pathlib.Path('/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence/run2.py')))))
'''.replace('JJ', repr(J)).replace('HH', repr(H)).replace('MODULES', repr(list(latest)))
remote = json.loads(subprocess.check_output(['ssh', HOST, 'python3 -'], input=remote_script, text=True))
final = []
for mod, rec in latest.items():
    pins = remote['modules'][mod]
    assert pins['deps_fingerprint'] == rec['deps_fingerprint'], mod
    assert pins['source']['sha256'] == rec['source_sha256'], mod
    m = mod.replace('.', '/')
    final.append(dict(**rec, **{'direct_imports': pins['direct_imports'], 'object': pins['object'],
        'launcher_command': ['sh', H+'/tools/run-joint.sh', str(rec['attempt']), m, 'J', '7000', '7', rec['deps_fingerprint']],
        'lean_command': [remote['environment']['LEAN'], '-j1', '-M7000', '-DElab.async=false', '-R', J+'/sources', '-o', J+'/objects/'+m+'.olean', J+'/sources/'+m+'.lean'],
        'scope': {'MemoryHigh': '5G', 'MemoryMax': '7G', 'MemorySwapMax': '0', 'TasksMax': 128}}))

# No existing Lean module or frozen source file may change in this job.
tracked = git('ls-files', 'docs/research/v8-r0-zk-20261009/lean',
    'docs/research/100bit-spend-path-20261013/lean', 'crates/aspis-r1-cost-probe',
    'programs/r1-cost-probe').decode().splitlines()
for path in tracked:
    assert (ROOT/path).read_bytes() == git('show', BASE+':'+path), path
pins = {p: {'sha256': sha((ROOT/p).read_bytes()), 'size': (ROOT/p).stat().st_size}
    for p in tracked if p.endswith('.rs')}
(PACKET/'source-pins.json').write_text(json.dumps(pins, indent=2)+'\n')
manifest = dict(schema='focused-extractor-proof-packet-v1', source_revision=BASE,
    source_dirty=True, environment='J', host=HOST, final_attempts=final,
    historical_attempts=[r['attempt'] for r in records if r['attempt'] not in {x['attempt'] for x in final}],
    environment_snapshot=remote['environment'], launcher=remote['launcher'], driver=remote['driver'],
    new_theorems=10, full_manifest_replay=False, existing_sources_unchanged=True)
(PACKET/'manifest.json').write_text(json.dumps(manifest, indent=2)+'\n')
result = dict(final_attempts={m: r['attempt'] for m,r in latest.items()},
    new_theorems=10, standard_axioms_only=True, swaps=0,
    existing_sources_compared=len(tracked), frozen_rust_pins=len(pins),
    deps_fingerprints_verified=True, source_hashes_verified=True)
(PACKET/'audit.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result, indent=2))
