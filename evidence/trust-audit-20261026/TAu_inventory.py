"""Read selected object/source metadata; generate only #print/#check audit inputs.
Run on the existing coherent host workspace; never rewrites dependency objects.
"""
from pathlib import Path
import hashlib,json,re
B=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')
E=B/'TAu_data';E.mkdir(exist_ok=True)
cfg=json.loads((B/'TAu_base.json').read_text()); roots=[Path(x) for x in cfg['env']['LEAN_PATH'].split(':')]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
raw=Path('/home/dombarker/project-offloads/codex-cx-import-union-20261022/evidence/raw-union-enumeration.jsonl')
graph={};decl={}
for line in raw.open():
 k,v=line.split(' ',1)
 if k=='RAW_MODULE':
  m,p,im=json.loads(v);graph[m]=dict(raw_path=p,imports=im)
 elif k=='RAW_DECL':
  n,m,kind=json.loads(v);decl.setdefault(m,[]).append([n,kind])
repo=json.loads((B/'TAu_repo.json').read_text())
manifest=json.loads((B/'object-source-manifest.json').read_text())['modules']
selected={};missing=[]
def visit(m):
 if m in selected:return
 key=m.replace('.','/')
 obj=next((p/(key+'.olean') for p in roots if (p/(key+'.olean')).exists()),None)
 if obj is None:missing.append(m);return
 candidates=[obj.with_suffix('.lean'),B/'source-inputs'/(key+'.lean')]
 if '/.lake/build/lib/lean/' in str(obj):candidates.append(Path(str(obj).replace('/.lake/build/lib/lean/','/')[:-6]+'.lean'))
 if '/lib/lean/' in str(obj) and str(obj).startswith('/home/dombarker/.elan/'):candidates.append(Path(str(obj).replace('/lib/lean/','/src/lean/')[:-6]+'.lean'))
 src=next((p for p in candidates if p.exists()),None)
 r=dict(module=m,object_path=str(obj),object_sha256=sha(obj),object_bytes=obj.stat().st_size)
 if src:
  text=src.read_text();r.update(source_path=str(src),source_sha256=sha(src),source_text=text)
 elif m in repo:
  r.update(source_path=repo[m]['path'],source_sha256=repo[m]['sha256'],source_text=repo[m]['text'],source_fallback=True)
 if 'source_text' in r:
  # Remove nested block comments before reading source imports.
  text=r['source_text'];clean=[];depth=0;i=0
  while i<len(text):
   if text[i:i+2]=='/-':depth+=1;i+=2
   elif depth and text[i:i+2]=='-/':depth-=1;i+=2
   else:
    if not depth:clean.append(text[i])
    i+=1
  text=''.join(clean)
  im=[]
  for line in text.splitlines():
   match=re.match(r'\s*(?:(?:public|private|meta)\s+)?import\s+(.+)',line)
   if match:im.extend(match[1].split('--')[0].split())
  if m!='Init' and not re.search(r'^prelude\b',text,re.M):im=['Init']+im
  r['imports']=list(dict.fromkeys(im));r['imports_basis']='source'
 elif m in manifest:
  r['imports']=manifest[m]['imports'];r['imports_basis']='pinned object manifest'
 elif m in graph:
  r['imports']=graph[m]['imports'];r['imports_basis']='reused raw object census'
 else:r.update(imports=[],imports_basis='MISSING');missing.append(m+':imports')
 r['raw_declarations']=decl.get(m,[])
 if m in graph:
  p=Path(graph[m]['raw_path']);r['census_same_object']=p.exists() and sha(p)==r['object_sha256']
 if m in manifest and manifest[m].get('sha256')==r['object_sha256']:
  r['imports']=manifest[m]['imports'];r['imports_basis']='hash-matched pinned object manifest'
 elif r.get('census_same_object'):
  r['imports']=graph[m]['imports'];r['imports_basis']='hash-matched raw object census'
 selected[m]=r
 for x in r['imports']:visit(x)
for m in ['FGl_Headline','Rc6_Top']:visit(m)
(E/'TAu_closure.json').write_text(json.dumps(dict(raw_census_sha256=sha(raw),modules=selected,missing=missing),indent=2)+'\n')
print(json.dumps(dict(modules=len(selected),missing=missing,with_source=sum('source_text' in r for r in selected.values()),census_same=sum(r.get('census_same_object',False) for r in selected.values()),axiom_declarations=[(m,n) for m,r in selected.items() for n,k in r['raw_declarations'] if k=='axiom']),indent=2))
