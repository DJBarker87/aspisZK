"""Freeze the exact merged sources, manifests, root union and import order."""
import pathlib,json,re,hashlib,subprocess
E=pathlib.Path('evidence/pv-lib-20261107/v1-coherence'); rev='9a38706526c45bc0fac071869458400a07aaaba7'
sha=lambda b:hashlib.sha256(b).hexdigest()
manifest=subprocess.check_output(['git','show','research:design/PRIVACY-LIBRARY-V1-20261108.json'])
(E/'V1_MANIFEST.json').write_bytes(manifest)
roots={};modules=set();inputs={}
def walk(x,origin):
 if isinstance(x,dict):
  for k,v in x.items():
   if k=='roots' and isinstance(v,list):
    for r in v:
     if isinstance(r,str):roots.setdefault(r,[]).append(origin)
   elif k=='modules' and isinstance(v,list):modules.update(v)
   elif k in ['theorem','law','model','root'] and isinstance(v,str) and '.' in v and re.fullmatch(r'[\w.\x27]+',v):roots.setdefault(v,[]).append(origin)
   walk(v,origin)
 elif isinstance(x,list):
  for v in x:walk(v,origin)
for p in sorted(pathlib.Path('evidence/pv-lib-20261107').rglob('*ROOTS.json')):
 if 'v1-coherence' in str(p):continue
 b=p.read_bytes();inputs[str(p)]=sha(b);walk(json.loads(b),str(p))
walk(json.loads(manifest),'v1 manifest')
pv=sorted(p.stem for p in pathlib.Path('lean').glob('PV_LIB_*.lean'));modules.update(pv)
sources={};external=set();order=[];active=set()
def visit(m):
 if m in sources or m in external:return
 p=pathlib.Path('lean',m.replace('.','/')+'.lean')
 if not p.exists():external.add(m);return
 assert m not in active,m
 active.add(m);b=subprocess.check_output(['git','show',rev+':'+str(p)]);deps=re.findall(r'^import\s+(\S+)',b.decode(),re.M)
 for d in deps:visit(d)
 sources[m]=dict(path=str(p),sha256=sha(b),imports=deps);order.append(m);active.remove(m)
for m in sorted(modules):visit(m)
x=dict(source_revision=rev,pv_modules=pv,root_provenance=roots,root_lists=inputs,modules=sorted(modules),sources=sources,order=order,external_imports=sorted(external))
(E/'INVENTORY.json').write_text(json.dumps(x,indent=2)+'\n')
print('PV',len(pv),'roots',len(roots),'closure',len(order),'external imports',len(external));print(sorted(external))
