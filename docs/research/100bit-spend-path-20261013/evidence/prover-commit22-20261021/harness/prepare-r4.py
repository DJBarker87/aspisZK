"""Inventory cached source dependency closure; copy no object over an existing one."""
from pathlib import Path
import subprocess,json,re,hashlib
E=Path(__file__).resolve().parent.parent
host='dombarker@100.108.41.90'
code='''from pathlib import Path
import json
J=Path('/home/dombarker/project-offloads/aspis-joint-20261019')
e=json.loads(Path('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json').read_text())
paths=[J/'objects']+[Path(x) for x in e['LEAN_PATH'].split(':')]
mods={}
for d in paths:
 if d.exists():
  for p in d.rglob('*.olean'):
   if p.exists():mods.setdefault(str(p.relative_to(d).with_suffix('')).replace('/','.'),str(p))
print(json.dumps(mods))
'''
remote=json.loads(subprocess.check_output(['ssh',host,'python3 -'],input=code,text=True))
roots=['R4TransportCircleCoordinates','R4Transport2CirclePrefix','R4Transport2WideReference','R4TransportGammaFold','R4Transport2QueryRho']
receipts=[Path('docs/research/100bit-spend-path-20261013/evidence/r4-transport-20261021/R4TransportCircleCoordinates-1/command.json'),Path('docs/research/100bit-spend-path-20261013/evidence/r4-transport2-20261021/R4Transport2CirclePrefix-1/command.json')]
paths=[]
for f in receipts:
 for s in json.loads(f.read_text())['lean_path'].split(':'):
  if Path(s).is_dir() and Path(s) not in paths:paths.append(Path(s))
sources=[Path(x) for x in subprocess.check_output(['rg','--files','-g','*.lean'],text=True).splitlines()]
seen=set();missing=[];existing=[];unresolved=[]
def visit(m):
 if m in seen:return
 seen.add(m)
 if m in remote:existing.append(dict(module=m,host_object=remote[m]));return
 rel=m.replace('.','/')+'.olean';p=next((d/rel for d in paths if (d/rel).exists()),None)
 if p is None:unresolved.append(dict(module=m,reason='no local object'));return
 suff=m.replace('.','/')+'.lean'
 matches=[s for s in sources if str(s).endswith('/'+suff)]
 preferred=[s for s in matches if str(s).startswith('docs/research/100bit-spend-path-20261013/lean/')]
 exact=Path('docs/research/100bit-spend-path-20261013/lean')/suff
 if not matches:
  matches=[s for s in sources if s.name==m.split('.')[-1]+'.lean' and ('.' not in m or 'namespace '+m.rsplit('.',1)[0] in s.read_text())]
 hashes={hashlib.sha256(s.read_bytes()).hexdigest() for s in matches}
 source=exact if exact.exists() else (matches[0] if len(hashes)==1 else None)
 if source is None:unresolved.append(dict(module=m,reason='ambiguous or absent source',candidates=[str(s) for s in matches][:8]));return
 missing.append(dict(module=m,object=str(p),object_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),source=str(source),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest()))
 for dep in re.findall(r'^import\s+(\S+)',source.read_text(),re.M):visit(dep)
for m in roots:visit(m)
result=dict(roots=roots,missing=missing,existing=existing,unresolved=unresolved,scope='Source-graph cache inventory only. No imported proof is re-certified and no shared object overwritten.')
(E/'r4-cache-inventory.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(missing=len(missing),existing=len(existing),unresolved=unresolved)))
