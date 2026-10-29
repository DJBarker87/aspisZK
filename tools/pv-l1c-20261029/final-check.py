"""Collect original logs and verify final sources, axioms and unchanged cohort."""
from pathlib import Path
import json,subprocess,hashlib,shlex,re
E=Path('evidence/pv-l1c-20261029');H='/home/dombarker/project-offloads/codex-pv-l1c-20261029';host='dombarker@100.108.41.90';sha=lambda b:hashlib.sha256(b).hexdigest()
plan=json.load(open(E/'build-plan.json'));accepted={};all_records=[];originals=[]
for f in sorted(E.glob('modules-*.json')):
 a=int(f.stem.split('-')[-1]);assert 65400<=a<=65499
 receipt=json.load(open(E/f'receipt-{a}.json'));assert receipt['launch_admission']['allowed'] is True
 records=json.load(open(f));assert len(records)==1
 for v in records:
  v=dict(v,attempt=a);all_records.append(v)
  if v['accepted']:accepted[v['module']]=v
  for kind in ['output','time']:
   originals.append(dict(remote=v[kind+'_path'],local=f'raw-{a}.{kind}',sha256=v[kind+'_sha256']))
assert len(all_records)<=100
checks=[]
for m,pin in plan['modules'].items():
 assert m in accepted,('not accepted',m)
 v=accepted[m];b=subprocess.check_output(['git','show','HEAD:'+pin['path']]);assert sha(b)==pin['sha256']==v['source_sha256']
 for a in v['axioms']:
  names=re.search(r'\[([\s\S]*?)\]',a)
  if names:assert set(re.findall(r'[A-Za-z.]+',names[1])) <= {'propext','Classical.choice','Quot.sound'},a
 checks.append(dict(module=m,source_path=pin['path'],source_sha256=v['source_sha256'],object_sha256=v['object_sha256'],dependencies=v['dependencies']))
queries='\n'.join(accepted['PV_L1C_Axioms']['axioms'])
names=[]
for f in Path('lean').glob('PV_L1C_*.lean'):
 s=f.read_text()
 for n in re.findall(r'^theorem (\w+)',s,re.M):
  assert '#print axioms '+n in s,(f,n)
  assert "'PV_L1C."+n+"'" in queries,n
  names.append('PV_L1C.'+n)
source_resolution=json.load(open(E/'source-resolution.json'));inh=source_resolution['projects']
code=r'''import json,sys,pathlib,hashlib
x=json.load(sys.stdin);p=pathlib.Path(x['H']);sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for v in x['checks']:
 assert sha(p/'sources'/(v['module']+'.lean'))==v['source_sha256']
 assert sha(p/'objects'/(v['module']+'.olean'))==v['object_sha256']
 for d,r in v['dependencies'].items():assert sha(pathlib.Path(r['path']))==r['sha256'],('dep',d)
for v in x['inherited'].values():assert sha(pathlib.Path(v['object_path']))==v['object_sha256'],('inherited',v['module'])
logs={}
for v in x['originals']:
 q=pathlib.Path(v['remote']);assert sha(q)==v['sha256'];logs[v['local']]=q.read_text()
print(json.dumps(dict(all_match=True,own=len(x['checks']),inherited=len(x['inherited']),logs=logs)))
'''
r=subprocess.run(['ssh',host,'python3 -c '+shlex.quote(code)],input=json.dumps(dict(H=H,checks=checks,inherited=inh,originals=originals)),text=True,capture_output=True);assert r.returncode==0,r.stderr
host_result=json.loads(r.stdout)
for n,t in host_result.pop('logs').items():(E/n).write_text(t)
changed=subprocess.check_output(['git','diff','--name-only','f2caad8ab2','HEAD'],text=True).splitlines();assert not any(p.startswith(('crates/','programs/')) for p in changed)
assert all(p.startswith(('lean/PV_L1C_','tools/pv-l1c-20261029/','evidence/pv-l1c-20261029/')) for p in changed),changed
assert all(p.stat().st_size<=20_000_000 for p in E.rglob('*') if p.is_file())
result=dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),host=host_result,Lean_starts=len(all_records),accepted_starts=sum(v['accepted'] for v in all_records),failed=[dict(attempt=v['attempt'],module=v['module'],source_revision=v['source_revision'],source_sha256=v['source_sha256'],exit=v['exit']) for v in all_records if not v['accepted']],accepted_modules=len(accepted),theorems=names,peak_rss_bytes=max(v['peak_rss_bytes'] for v in all_records),total_module_wall_seconds=sum(v['wall_seconds'] for v in all_records),swaps=sum(v['swaps'] for v in all_records),native_scopes=0,Kani=0,admission_slips=0,refusals=len(list(E.glob('refusal-*.json'))),audits=[dict(attempt=v['attempt'],module=v['module'],source_revision=v['source_revision'],exit=v['exit'],wall_seconds=v['wall_seconds'],peak_rss_bytes=v['peak_rss_bytes'],swaps=v['swaps'],axioms=v['axioms']) for v in all_records if v['attempt']>=65497],checks=checks)
(E/'final-validation.json').write_text(json.dumps(result,indent=2)+'\n')
(E/'COMMITS.txt').write_text(subprocess.check_output(['git','log','--oneline','f2caad8ab2..HEAD'],text=True))
print(json.dumps({k:result[k] for k in ['Lean_starts','accepted_starts','accepted_modules','peak_rss_bytes','total_module_wall_seconds','swaps','admission_slips']}))
