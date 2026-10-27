"""Resolve project source closure in the lead's h4/h5/h5' authority order."""
from pathlib import Path
import subprocess,json,hashlib,re,sys
D=Path(__file__).resolve().parent
rev=subprocess.check_output(['git','rev-parse','HEAD']).decode().strip()
def gitobj(key):return subprocess.check_output(['git','show',key])
inv=json.loads(Path('evidence/envj-rebuild-20261026/EJR_final-inventory.json').read_text())
ejr={r['module'].replace('/','.'):r for r in inv['selected'] if r.get('resolution')}
ext={r['module'].replace('/','.') for r in json.loads((D/'d324-external-object-manifest.json').read_text())}
freezes={}
for n in ['prover-commit47-20261022/final-source-freeze.json','prover-commit48-20261022/pins/final-source-freeze.json']:
 p=Path('docs/research/100bit-spend-path-20261013/evidence')/n
 for r in json.loads(p.read_text()).get('sources',[]):freezes.setdefault(r['module'],(r,str(p)))
paths=subprocess.check_output(['git','ls-files','*.lean','*.lean.host.txt']).decode().splitlines()
resolved={};missing=[];order=[];active=set()
def resolve(m):
 if m in ext or m in resolved:return
 if m in active:raise RuntimeError('cycle '+m)
 active.add(m)
 if m in ejr:
  r=ejr[m];p=r['resolution']['path'];blob=r['resolution']['blob'];data=gitobj(blob);kind='EJR';assert hashlib.sha256(data).hexdigest()==r['sha256'],m
 elif m in freezes:
  r,record=freezes[m];p=r['path'];data=gitobj('HEAD:'+p);blob=subprocess.check_output(['git','rev-parse','HEAD:'+p]).decode().strip();kind='freeze '+record;assert hashlib.sha256(data).hexdigest()==r['sha256'],m
 else:
  suffix=m.replace('.','/')+'.lean';candidates=[p for p in paths if p.endswith('/'+suffix) or p==suffix]
  if not candidates and m.startswith('R1Z.'):
   candidates=[p for p in paths if p.endswith('/'+m[4:]+'.lean') and '/lean/prover-rw-20261023/' in p]
  if not candidates and m.startswith('PV_B3_'):candidates=[str(D/'lean'/(m+'.lean'))]
  if len(candidates)!=1:
   missing.append({'module':m,'candidates':candidates});active.remove(m);return
  p=candidates[0];data=gitobj('HEAD:'+p);blob=subprocess.check_output(['git','rev-parse','HEAD:'+p]).decode().strip();kind='h5 HEAD'
 imports=re.findall(r'^import\s+(\S+)',data.decode(),re.M)
 tracked=[p1 for p1 in paths if p1.endswith('/'+m.replace('.','/')+'.lean')]
 conflicts=[{'path':p1,'sha256':hashlib.sha256(gitobj('HEAD:'+p1)).hexdigest()}for p1 in tracked if hashlib.sha256(gitobj('HEAD:'+p1)).digest()!=hashlib.sha256(data).digest()]
 resolved[m]={'module':m,'path':p,'blob':blob,'sha256':hashlib.sha256(data).hexdigest(),'authority':kind,'imports':imports,'tracked_conflicts':conflicts}
 for imp in imports:resolve(imp)
 active.remove(m);order.append(m)
for m in sys.argv[1:]:resolve(m)
out={'revision':rev,'roots':sys.argv[1:],'modules':resolved,'topological_order':order,'unresolved':missing,'external_authority':'h4 replay manifest; already SHA checked'}
(D/'d324-project-resolution.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'count':len(resolved),'unresolved':missing,'h5':sum(r['authority']=='h5 HEAD' for r in resolved.values()),'order':order},indent=2))
