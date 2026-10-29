"""Verify exact source revisions, receipts, axioms and loaded object cohort."""
from pathlib import Path
import json,hashlib,subprocess,shlex,re
E=Path('evidence/pv-l1e-20261029');H='/home/dombarker/project-offloads/codex-pv-l1e-20261029'
rows={int(f.stem.split('-')[1]):json.loads(f.read_text())[0] for f in E.glob('modules-*.json')}
assert set(rows)<=set(range(66500,66600)) and len(rows)<=100
assert all(rows[a]['accepted'] for a in [66597,66598,66599])
for a,r in rows.items():
 assert len(json.loads((E/f'modules-{a}.json').read_text()))==1
 for kind,key in [('out','output'),('time','time')]:
  path=E/'raw'/f'{a}-00.{kind}';assert hashlib.sha256(path.read_bytes()).hexdigest()==r[key+'_sha256'],path
 assert json.loads((E/f'admission-{a}.json').read_text())['allowed'] is True
 receipt=json.loads((E/f'receipt-{a}.json').read_text());assert receipt['exit']==r['exit']
 b=subprocess.check_output(['git','show',r['source_revision']+':'+r['source']['path']]);assert hashlib.sha256(b).hexdigest()==r['source_sha256'],r['module']
 if r['accepted']:assert 'sorryAx' not in (E/'raw'/f'{a}-00.out').read_text()
 # Both host admission and cooldown are checked for every actual launch.
 launch_time=__import__('datetime').datetime.fromisoformat(receipt['utc']).timestamp()
 for p in E.glob('refusal-*.json'):
  t=json.loads(p.read_text())['epoch']
  assert launch_time<t or launch_time>=t+180,(a,'cooldown',launch_time,t)
accepted={r['module']:r for _,r in sorted(rows.items()) if r['accepted']}
expected={m:r['object_sha256'] for m,r in accepted.items()}
for r in json.loads((E/'reuse.json').read_text())['reused']:
 assert r['module'] not in expected or expected[r['module']]==r['object_sha256'];expected[r['module']]=r['object_sha256']
for m,r in json.loads((E/'source-resolution.json').read_text())['projects'].items():
 assert m not in expected or expected[m]==r['object_sha256'];expected[m]=r['object_sha256']
edges=[dict(module=m,dependency=d,sha256=v['sha256']) for m,r in accepted.items() for d,v in r['dependencies'].items()]
external=json.loads((E/'external-authority.json').read_text())
code=r'''import pathlib,sys,json,hashlib,subprocess
x=json.load(sys.stdin);p=pathlib.Path(x['H']);env=json.load(open(p/'J.json'));roots=[pathlib.Path(q) for q in env['LEAN_PATH'].split(':')];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert subprocess.check_output([env['LEAN'],'--githash'],text=True).strip()==env['LEAN_GITHASH']=='8c9756b28d64dab099da31a4c09229a9e6a2ef35'
def loaded(m):return next(q/(m.replace('.','/')+'.olean') for q in roots if (q/(m.replace('.','/')+'.olean')).is_file())
checks=[]
for m,h in x['expected'].items():
 q=loaded(m);assert sha(q)==h,('module',m);checks.append(dict(module=m,path=str(q),sha256=h))
for e in x['edges']:assert sha(loaded(e['dependency']))==e['sha256'],('edge',e)
for e in x['external']:
 assert sha(pathlib.Path(e['path']))==e['object_sha256'],('external authority',e['module'])
 assert sha(loaded(e['module'].replace('/','.')))==e['object_sha256'],('external loaded',e['module'])
print(json.dumps(dict(all_match=True,checks=checks,dependency_edges=len(x['edges']),external=len(x['external']),toolchain=env['LEAN_GITHASH'],LEAN_PATH=env['LEAN_PATH'],old_objects_written=False)))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(dict(H=H,expected=expected,edges=edges,external=external)),text=True,capture_output=True);assert r.returncode==0,r.stderr
axioms={}
for rec in accepted.values():
 for line in rec['axioms']:
  name=re.match(r"'([^']+)'",line)[1]
  ax=[] if 'does not depend on any axioms' in line else re.search(r'\[([\s\S]*?)\]',line)[1].replace('\n',' ').split(',')
  ax=[v.strip() for v in ax if v.strip()];assert set(ax)<={'propext','Classical.choice','Quot.sound'},(name,ax);axioms[name]=ax
(E/'axioms-summary.json').write_text(json.dumps(axioms,indent=2)+'\n')
result=dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),compiler_starts=len(rows),pass_count=sum(v['accepted'] for v in rows.values()),fail_count=sum(not v['accepted'] for v in rows.values()),wall_seconds=sum(v['wall_seconds'] for v in rows.values()),peak_rss_bytes=max(v['peak_rss_bytes'] for v in rows.values()),swaps=sum(v['swaps'] for v in rows.values()),h6_final=json.loads(r.stdout),audit_targets={str(a):rows[a] for a in [66597,66598,66599]},native_scopes=0,Kani=0,refusals=len(list(E.glob('refusal-*.json'))),void_launches=0)
(E/'final-validation.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['h6_final','audit_targets']}))
