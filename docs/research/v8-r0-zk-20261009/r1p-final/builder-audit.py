#!/usr/bin/env python3
"""Audit the builder extension's focused receipts without running Lean."""
import hashlib, json, pathlib, re, subprocess
HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parents[3]
HOST = 'dombarker@100.108.41.90'
J = '/home/dombarker/project-offloads/aspis-joint-20261019'
MODULES = ['R1Z.BuilderRefinement','R1Z.BuilderSemanticBridge',
           'R1Z.BuilderSpendRelation','R1Z.BuilderCanonical','R1Z.BuilderSource',
           'R1Z.BuilderTransportExtracted','R1Z.BuilderTransport']
records = [json.loads(x) for x in (HERE/'attempts.jsonl').read_text().splitlines()
           if 8400 <= json.loads(x)['attempt'] <= 8599]
latest = {r['module']:r for r in records}
final = {}
count = 0
for m in MODULES:
    r = latest[m]
    p = ROOT/'docs/research/v8-r0-zk-20261009/lean'/(m.replace('.','/')+'.lean')
    s = p.read_text()
    assert r['exit'] == 0 and r['swaps'] == '0' and not r['errors'], m
    assert hashlib.sha256(p.read_bytes()).hexdigest() == r['source_sha256'], m
    assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b', re.sub(r'/\-.*?\-/', '', '\n'.join(
        l for l in s.splitlines() if not l.startswith('--')), flags=re.S)), m
    for t in re.findall(r'^theorem (\w+)', s, re.M):
        assert any('.'+t+"'" in a for a in r['axioms']), (m,t)
        count += 1
    for a in r['axioms']:
        x = re.search(r'\[(.*)\]', a)
        if x: assert set(x.group(1).split(', ')) <= {'propext','Classical.choice','Quot.sound'}
    final[m] = r
script = '''import pathlib,hashlib,json,re
J=pathlib.Path(JJ)
def pin(p):
 return dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size=p.stat().st_size) if p.exists() else dict(sha256='missing',size=None)
r={}
for m in MODS:
 src=J/'sources'/(m.replace('.','/')+'.lean')
 deps={d:pin(J/'objects'/(d.replace('.','/')+'.olean')) for d in sorted(re.findall(r'^import (\\S+)',src.read_text(),re.M))}
 fp=hashlib.sha256(';'.join(d+'='+p['sha256'] for d,p in deps.items()).encode()).hexdigest()[:16]
 r[m]=dict(source=pin(src),object=pin(J/'objects'/(m.replace('.','/')+'.olean')),direct_imports=deps,deps_fingerprint=fp)
print(json.dumps(r))
'''.replace('JJ',repr(J)).replace('MODS',repr(MODULES))
pins = json.loads(subprocess.check_output(['ssh',HOST,'python3 -'],input=script,text=True))
for m,r in final.items():
    assert pins[m]['deps_fingerprint'] == r['deps_fingerprint'], m
    assert pins[m]['source']['sha256'] == r['source_sha256'], m
    pins[m]['attempt'] = r['attempt']
    pins[m]['axioms'] = r['axioms']
    pins[m]['source_revision'] = r['source_revision']
    pins[m]['source_dirty'] = r['source_dirty']
    pins[m]['wall'] = r['wall']
    pins[m]['peak_rss_kib'] = r['peak_rss_kib']
    pins[m]['swaps'] = r['swaps']
    pins[m]['exit'] = r['exit']
    pins[m]['command'] = ['sh','/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/tools/run-joint.sh',str(r['attempt']),m.replace('.','/'),'J','7000','7',r['deps_fingerprint']]
changed = subprocess.check_output(['git','diff','--name-only','9ba738457','--','crates','programs','docs/research/v8-r0-zk-20261009/lean','docs/research/100bit-spend-path-20261013/lean'],cwd=ROOT,text=True).splitlines()
authorized_rust = {'crates/aspis-statement/src/pool_v1/pair_forest_trace.rs',
                   'crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs'}
expected = {'docs/research/v8-r0-zk-20261009/lean/'+m.replace('.','/')+'.lean' for m in MODULES}
# git diff omits new untracked files until staged.
assert set(changed) <= expected | authorized_rust, changed
result = dict(schema='builder-refinement-focused-v1',base='9ba738457',modules=pins,
              theorem_count=count,standard_axioms_only=True,existing_sources_unchanged=False,authorized_rust_changes=sorted(authorized_rust),
              frozen_manifest_replayed=False,scope=dict(MemoryHigh='5G',MemoryMax='7G',MemorySwapMax='0',TasksMax=128))
(HERE/'builder-audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(theorems=count,final_attempts={m:r['attempt'] for m,r in final.items()},standard_axioms_only=True),indent=2))
