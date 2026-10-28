"""Read-only source and object inventory for the inherited private cache."""
from pathlib import Path
import json,subprocess,shlex,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-l2c-20261028'
label=sys.argv[1] if len(sys.argv)>1 else 'focused'
r=json.loads((E/(label+'-resolution.json')).read_text());mods={m:v for m,v in r['resolved'].items() if 'imports' in v}
code='''import pathlib,json,sys,hashlib
H=pathlib.Path('/home/dombarker/project-offloads/codex-pv-runjoin-20261026');e=json.load(open(H/'runjoin24-lean/J.json'));roots=[pathlib.Path(x) for x in e['LEAN_PATH'].split(':')];out=[]
for m,v in json.load(sys.stdin).items():
 rel=m.replace('.','/');o=next((root/(rel+'.olean') for root in roots if (root/(rel+'.olean')).is_file()),None)
 if o is None:
  out.append(dict(module=m,missing=True));continue
 real=o.resolve();s=pathlib.Path(str(real).replace('/objects/','/sources/').replace('/lean-objects/','/sources/')).with_suffix('.lean')
 if not s.is_file():
  for q in [s.with_suffix('.lean.txt'),H/'sources'/(rel.replace('/','.')+'.lean'),H/'sources'/(rel.replace('/','.')+'.lean.txt')]:
   if q.is_file():s=q;break
 sh=hashlib.sha256(s.read_bytes()).hexdigest() if s.is_file() else None
 out.append(dict(module=m,object_path=str(o),object_realpath=str(real),object_sha256=hashlib.sha256(o.read_bytes()).hexdigest(),source_path=str(s),source_sha256=sh,expected_sha256=v['sha256'],source_match=sh==v['sha256'],authority=v['authority']))
print(json.dumps(out))
'''
p=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(mods),text=True,capture_output=True);assert p.returncode==0,p.stderr
out=json.loads(p.stdout)
prior={}
for f in (R/'evidence').glob('pv-runjoin*/receipt-*.json'):
 try:x=json.loads(f.read_text())
 except (ValueError,OSError):continue
 if not isinstance(x,dict):continue
 if x.get('exit') not in [0,['exit=0']] or 'sorryAx' in str(x.get('axioms')):continue
 sha=x.get('source_sha256');snapshot=f.parent/x.get('source_snapshot','')
 if sha and snapshot.is_file():
  import hashlib
  if hashlib.sha256(snapshot.read_bytes()).hexdigest()==sha:prior.setdefault(sha,[]).append(str(f.relative_to(R)))
for x in out:
 if not x.get('source_match') and x.get('expected_sha256') in prior:
  x['prior_own_source_receipts']=prior[x['expected_sha256']];x['retained_own_cache_source_match']=True
(E/(label+'-project-cache-check.json')).write_text(json.dumps(out,indent=2)+'\n')
unmatched=[x['module'] for x in out if not (x.get('source_match') or x.get('retained_own_cache_source_match'))]
print('project source checks',len(out),'unmatched',unmatched)
