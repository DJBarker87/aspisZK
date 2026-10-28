"""Compile focused prerequisites, dependent bridges, then one final axioms manifest."""
from pathlib import Path
import json,subprocess,hashlib,time,sys,shlex
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-kstub-20261028';D='/home/dombarker/project-offloads/codex-pv-kstub-20261028';H='dombarker@100.108.41.90'
names=['AppendDomain','CopyWindows','CopyEquality','AppendCoordinates','OptionCoordinates','SplitCoverage','AppendBridge','Final'];pins=[]
selected=list(enumerate(names,44703))
if '--resume-parser-fix' in sys.argv:selected=list(enumerate(['AppendCoordinates','SplitCoverage','AppendBridge','Final'],44707))
for i,n in selected:
 module='PV_KStub_'+n;p=R/'tools/pv-kstub-20261028'/(module+'.lean');rel=str(p.relative_to(R));data=p.read_bytes();tracked=subprocess.check_output(['git','show','HEAD:'+rel],cwd=R);assert data==tracked
 pins.append(dict(id=i,module=module,path=rel,blob=subprocess.check_output(['git','rev-parse','HEAD:'+rel],cwd=R,text=True).strip(),sha256=hashlib.sha256(data).hexdigest(),revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),source=data.decode()))
(E/'lean-continuation-plan.json').write_text(json.dumps([{k:v for k,v in p.items() if k!='source'} for p in pins],indent=2)+'\n')
code='''from pathlib import Path
import json,hashlib,re,os
D=Path('/home/dombarker/project-offloads/codex-pv-kstub-20261028')
pins=json.loads(PAYLOAD)
used=[]
scanned=[]
for base in Path('/home/dombarker/project-offloads').glob('codex-pv-*'):
 scanned.append(str(base))
 for root,dirs,files in os.walk(base):
  depth=len(Path(root).relative_to(base).parts)
  dirs[:]=[d for d in dirs if d not in ['target','node_modules','.git','sources','lean-sources','native','src','lean-objects','objects'] and depth<3]
  for name in dirs+files:
   if any(re.search(r'(?<![A-Za-z0-9])'+str(p['id'])+r'(?![A-Za-z0-9])',name) for p in pins):used.append(str(Path(root)/name))
for base in ['aspis-fs-generic-20261006','r1-privacy-build-integration-20261019']:
 for relative in ['sent.txt','evidence/sent.txt']:
  sent=Path('/home/dombarker/project-offloads')/base/relative
  if sent.exists():
   for line in sent.read_text().splitlines():
    if any(re.search(r'(?<![A-Za-z0-9])'+str(p['id'])+r'(?![A-Za-z0-9])',line) for p in pins):used.append(str(sent)+':'+line)
assert not used,used
checks=[]
for x in json.loads((D/'external-object-manifest.json').read_text()):
 if any(x['module']==prefix or x['module'].startswith(prefix+'/') for prefix in ['Init','Std','Lean','Lake']):
  h=hashlib.sha256(Path(x['path']).read_bytes()).hexdigest();assert h==x['object_sha256'],x['module'];checks.append(dict(module=x['module'],sha256=h,ok=True))
private_cache=[]
for module,expected in [('PV_KStub_CopyWindows','b11bc91acb1d03e19707b0ff27cd0a7c1f96b551151bd803c75f0325ab50e778'),('PV_KStub_CopyEquality','edb89a4fc7f7f717d97605269f0e4a422c8b829c3053a00f96e04d02282e3af6'),('PV_KStub_CopyMeaning','2baec49a3446a3bbb2be6f992c97d0a6897534a1cd308db8746194dedf665f2b'),('PV_KStub_WindowFrame','37fc1b48fa430b433b4c7e875fe7690fffb9eda336da549dc3570cd5a9c50911')]:
 source=D/(module+'.lean');obj=D/'lean-objects'/(module+'.olean')
 assert hashlib.sha256(source.read_bytes()).hexdigest()==expected
 private_cache.append(dict(module=module,source_sha256=expected,object_sha256=hashlib.sha256(obj.read_bytes()).hexdigest(),original_receipt={'PV_KStub_CopyMeaning':'44700','PV_KStub_WindowFrame':'44701','PV_KStub_CopyWindows':'44704','PV_KStub_CopyEquality':'44705'}[module]))
for p in pins:
 assert hashlib.sha256(p['source'].encode()).hexdigest()==p['sha256'];(D/(p['module']+'.lean')).write_text(p['source'])
env=json.loads((D/'env-J.json').read_text());env['LEAN_PATH']=str(D/'lean-objects')+':'+env['LEAN_PATH'];(D/'env-J-continuation.json').write_text(json.dumps(env,indent=2))
record=dict(private_cache=private_cache,receipt_directories_scanned=scanned,ids=[p['id'] for p in pins],other_receipt_conflicts=used,external_objects=checks,private_dependency_sources=[p['module'] for p in pins]+['PV_KStub_CopyMeaning','PV_KStub_WindowFrame'])
(D/'lean-continuation-preflight.json').write_text(json.dumps(record,indent=2));print(json.dumps(record))
'''.replace('PAYLOAD',repr(json.dumps(pins)))
for k in range(11):
 q=subprocess.run(['ssh',H,'python3 -'],input=code,text=True,capture_output=True)
 if q.returncode!=255:break
 with (E/'lean-continuation-transport.jsonl').open('a') as f:f.write(json.dumps(dict(exit=255,attempt=k,stderr=q.stderr,time=time.time()))+'\n')
 if k<10:time.sleep(60)
assert q.returncode==0,q.stderr
(E/'lean-continuation-preflight.json').write_text(q.stdout)
for p in pins:
 n=str(p['id']);m=p['module'];cmd=['timeout','900','python3','/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence/run2.py',D+'/env-J-continuation.json',D+'/lean-objects',D,D+'/lean-objects/'+m+'.olean',D+'/'+m+'.lean','7000']
 assert not (E/n/'receipt.json').exists()
 for k in range(11):
  q=subprocess.run([sys.executable,str(R/'tools/pv-kstub-20261028/scope.py'),n,'Lean',*cmd])
  if q.returncode==79:time.sleep(60);continue
  if q.returncode!=78:break
  if k<10:time.sleep(180)
 f=E/n/'receipt.json'
 if not f.exists():raise RuntimeError('Unresolved Lean attempt; recover before retry')
 receipt=json.loads(f.read_text());receipt.update({k:v for k,v in p.items() if k!='source'});receipt['external_preflight']='lean-continuation-preflight.json';f.write_text(json.dumps(receipt,indent=2)+'\n')
 if receipt['exit']!=0:sys.exit('Focused Lean error; correct source before proceeding')
