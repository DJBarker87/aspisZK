"""Resolve project source closure in the lead's h4/h5/h5' authority order."""
from pathlib import Path
import subprocess,json,hashlib,re,sys
D=Path('evidence/pv-b3p6-20261028')
rev=subprocess.check_output(['git','rev-parse','HEAD']).decode().strip()
def gitobj(key):return subprocess.check_output(['git','show',key])
inv=json.loads(Path('evidence/envj-rebuild-20261026/EJR_final-inventory.json').read_text())
ejr={r['module'].replace('/','.'):r for r in inv['selected'] if r.get('resolution')}
ejs={r['module'].replace('/','.'):r for r in json.loads(Path('evidence/envj-rebuild2-20261026/EJS_frontier-inventory.json').read_text())['ready']}
for r in json.loads(Path('evidence/envj-rebuild2-20261026/EJS_missing-extension-payload.json').read_text())['rows']:
 ejs.setdefault(r['module'].replace('/','.'),r)
ext={r['module'].replace('/','.') for r in json.loads((D/'external-object-manifest.json').read_text())}
freezes={}
for n in ['prover-commit47-20261022/final-source-freeze.json','prover-commit48-20261022/pins/final-source-freeze.json']:
 p=Path('docs/research/100bit-spend-path-20261013/evidence')/n
 for r in json.loads(p.read_text()).get('sources',[]):freezes.setdefault(r['module'],(r,str(p)))
paths=subprocess.check_output(['git','ls-files','*.lean','*.lean.host.txt','*.lean.txt']).decode().splitlines()
def strip_comments(s):
 out=[];i=0;depth=0
 while i<len(s):
  if s[i:i+2]=='/-':depth+=1;out.extend('  ');i+=2
  elif depth and s[i:i+2]=='-/':depth-=1;out.extend('  ');i+=2
  elif not depth and s[i:i+2]=='--':
   j=s.find('\n',i)
   if j<0:break
   out.extend(' '*(j-i));i=j
  else:
   out.append('\n' if s[i]=='\n' else (' ' if depth else s[i]));i+=1
 return ''.join(out)
resolved={};missing=[];order=[];active=set()
def resolve(m):
 if m in ext or m in resolved:return
 if m in active:raise RuntimeError('cycle '+m)
 active.add(m)
 if m in ejr:
  r=ejr[m];p=r['resolution']['path'];blob=r['resolution']['blob'];data=gitobj(blob);kind='EJR';assert hashlib.sha256(data).hexdigest()==r['sha256'],m
 elif m in ejs:
  r=ejs[m];p=r['path'];blob=r['blob'];data=gitobj(blob);kind='EJS frontier rebuild2';assert hashlib.sha256(data).hexdigest()==r['source_sha256'],m
 elif m in freezes:
  r,record=freezes[m];p=r['path'];data=gitobj('HEAD:'+p);blob=subprocess.check_output(['git','rev-parse','HEAD:'+p]).decode().strip();kind='freeze '+record;assert hashlib.sha256(data).hexdigest()==r['sha256'],m
 else:
  suffix=m.replace('.','/')+'.lean';candidates=[p for p in paths if p.endswith('/'+suffix) or p==suffix]
  if not candidates:
   candidates=[p for p in paths if p.endswith('/'+m+'.lean.txt')]
  if not candidates and m.startswith('R1Z.'):
   candidates=[p for p in paths if p.endswith('/'+m[4:]+'.lean') and '/lean/prover-rw-20261023/' in p]
  if m.startswith('PV_B3P_'):candidates=[str(D/'lean'/(m+'.lean'))] # Explicit own module registry; resolved/ is a receipt snapshot, not a source root.
  if len(candidates)>1:
   hashes={p1:hashlib.sha256(gitobj('HEAD:'+p1)).hexdigest() for p1 in candidates}
   if len(set(hashes.values()))==1:candidates=[sorted(candidates,key=lambda p1:('/lean/' not in p1,p1))[0]]
  if len(candidates)!=1:
   missing.append({'module':m,'candidates':candidates,'candidate_hashes':{p1:hashlib.sha256(gitobj('HEAD:'+p1)).hexdigest() for p1 in candidates}});active.remove(m);return
  p=candidates[0];data=gitobj('HEAD:'+p);blob=subprocess.check_output(['git','rev-parse','HEAD:'+p]).decode().strip();kind='h5 HEAD'
 imports=re.findall(r'^import\s+(\S+)',strip_comments(data.decode()),re.M)
 tracked=[p1 for p1 in paths if p1.endswith('/'+m.replace('.','/')+'.lean')]
 conflicts=[{'path':p1,'sha256':hashlib.sha256(gitobj('HEAD:'+p1)).hexdigest()}for p1 in tracked if hashlib.sha256(gitobj('HEAD:'+p1)).digest()!=hashlib.sha256(data).digest()]
 resolved[m]={'module':m,'path':p,'blob':blob,'sha256':hashlib.sha256(data).hexdigest(),'authority':kind,'imports':imports,'tracked_conflicts':conflicts}
 for imp in imports:resolve(imp)
 active.remove(m);order.append(m)
for m in sys.argv[1:]:resolve(m)
out={'revision':rev,'roots':sys.argv[1:],'modules':resolved,'topological_order':order,'unresolved':missing,'external_authority':'h4 replay manifest; already SHA checked'}
(D/'project-resolution227-carrier.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'count':len(resolved),'unresolved':missing,'h5':sum(r['authority']=='h5 HEAD' for r in resolved.values()),'order':order},indent=2))
