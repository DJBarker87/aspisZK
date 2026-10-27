#!/usr/bin/env python3
"""Replay genuinely changed dependency closures, never a nonce-based retry."""
import pathlib,json,subprocess,os,hashlib,sys
root=pathlib.Path(__file__).resolve().parents[2];e=root/'evidence/pv-srcid3-20261026'
plan=json.loads((e/'resume6-plan.json').read_text());rows={r['module']:r for r in plan['rows']};graph=json.loads((e/'resume6-binary-import-graph.json').read_text());edges={r['module']:r['imports'] for r in graph['modules']};initial={r['module']:r for r in json.loads((e/'resume6-package-closure.json').read_text())['objects']}
rejected={r['attempt'] for r in json.loads((e/'resume6-rejected-profiles.json').read_text())}
a=[json.loads(x) for x in (e/'resume6-attempts.jsonl').read_text().splitlines()];latest={}
for r in a:
 if r['exit']==0 and not r['nonstandard_axioms'] and r['attempt'] not in rejected and r.get('object_sha256'):latest[r['module'].replace('/','.')]=r
changed={m:r['object_sha256'] for m,r in latest.items() if m in initial and initial[m]['object_sha256']!=r['object_sha256']}
# Confirm that each purported changed object is still the effective input.
code='''import pathlib,json,hashlib
h=pathlib.Path('/home/dombarker/project-offloads');env=json.loads((h/'r1-privacy-build-integration-20261019/env/J.json').read_text());roots=[str(h/'aspis-joint-20261019/objects')]+env['LEAN_PATH'].split(':');out={}
for m in MODS:
 rel=m.replace('.','/')+'.olean';p=next((pathlib.Path(r)/rel for r in roots if (pathlib.Path(r)/rel).is_file()),None)
 out[m]=hashlib.sha256(p.read_bytes()).hexdigest() if p else None
print(json.dumps(out))
'''.replace('MODS',repr(sorted(changed)))
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -'],input=code,text=True,capture_output=True,check=True);current=json.loads(r.stdout);changed={m:h for m,h in changed.items() if current[m]==h}
tainted={'R1NaturalProjection'}
while True:
 n=len(tainted);tainted.update(m for m,deps in edges.items() if set(deps)&tainted)
 if len(tainted)==n:break
memo={}
def closure(m):
 if m in memo:return memo[m]
 out=set()
 for x in edges.get(m,[]):out.add(x);out.update(closure(x))
 memo[m]=out;return out
queue=[]
for r in graph['modules']:
 m=r['module']
 if m in rows and m not in tainted and set(changed)&closure(m):queue.append(m)
(e/'resume6-cohort-plan.json').write_text(json.dumps(dict(changed_inputs=[dict(module=m,before=initial[m]['object_sha256'],after=h) for m,h in changed.items()],tainted_projection_modules=sorted(tainted),order=queue,reason='Actual imported object bytes differ from the initial audited cache; complete transitive fingerprints capture changes hidden behind byte-identical import-only modules.'),indent=2)+'\n')
for m in queue:
 a=[json.loads(x) for x in (e/'resume6-attempts.jsonl').read_text().splitlines()]
 if len(a)>=int(sys.argv[1]):break
 # Existing successful/failed module attempts are left for a specifically reviewed retry.
 if any(x['module']==m.replace('.','/') for x in a):continue
 seen=e/'resume6-cohort-launch-results.jsonl';done=[json.loads(x) for x in seen.read_text().splitlines()] if seen.exists() else []
 if any(x['module']==m for x in done):continue
 evidence=[dict(module=x,before=initial[x]['object_sha256'],after=changed[x]) for x in sorted(set(changed)&closure(m))]
 assert evidence
 with (e/'resume6-cohort-input-changes.jsonl').open('a') as f:f.write(json.dumps(dict(module=m,changed_transitive_inputs=evidence))+'\n')
 env=dict(os.environ,PV_SRCID6_CLOSURE='1')
 r=subprocess.run([sys.executable,str(root/'tools/pv-srcid3/resume6-run-one.py'),m],env=env)
 with seen.open('a') as f:f.write(json.dumps(dict(module=m,exit=r.returncode))+'\n')
 if r.returncode:sys.exit(r.returncode)
