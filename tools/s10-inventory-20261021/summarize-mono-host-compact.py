#!/usr/bin/env python3
"""Hash and summarize complete entrypoint extraction attempts; preserve gaps."""
import collections,hashlib,json,sys
from pathlib import Path
H=Path('/home/dombarker/project-offloads/codex-cx-s10-inventory-20261021')
sha=lambda b:hashlib.sha256(b).hexdigest()
def walk(v,path=()):
 if isinstance(v,dict):
  yield path,v
  for k,z in v.items():yield from walk(z,path+(k,))
 elif isinstance(v,list):
  for i,z in enumerate(v):yield from walk(z,path+(i,))
def canonical(v):return json.dumps(v,sort_keys=True,separators=(',',':')).encode()
def textname(name):
 return '::'.join(n['Ident'][0] if 'Ident' in n else next(iter(n))+'#'+sha(canonical(n))[:16] for n in name)
for name in sys.argv[1:]:
 p=H/name/'Program.llbc'
 if not p.exists():print(name,'no LLBC',flush=True);continue
 raw=p.read_bytes();pin=dict(path=str(p),sha256=sha(raw),bytes=len(raw));x=json.loads(raw);del raw
 t=x['translated'];rows=[];hashcons={}
 # Resolve deduplicated function/type values before taking any canonical hashes.
 for path,v in walk(x):
  if 'HashConsedValue' in v:
   i,val=v['HashConsedValue'];assert i not in hashcons or hashcons[i]==val;hashcons[i]=val
 def expand(v):
  if isinstance(v,dict):
   if 'Deduplicated' in v:return expand(hashcons[v['Deduplicated']])
   if 'HashConsedValue' in v:return expand(v['HashConsedValue'][1])
   return {k:expand(z) for k,z in v.items()}
  if isinstance(v,list):return [expand(z) for z in v]
  return v
 for f in t['fun_decls']:
  if not f:continue
  m=f['item_meta'];span=m['span']['data'];file=t['files'][span['file_id']];calls=[];other=[]
  for path,v in walk(f['body']):
   if 'Call' in v:
    c=v['Call']['call'];func=expand(c['func']);reg=func.get('Regular',{});kind=reg.get('kind',{});fun=kind.get('Fun',{})
    calls.append(dict(path=list(path),function_sha256=sha(canonical(func)),target=fun.get('Regular'),kind='direct' if 'Regular' in fun else 'builtin' if 'Builtin' in fun else 'indirect_or_trait'))
   # Address-taken function refs are not calls, but must be retained as graph frontiers.
   if 'FnPtr' in v:other.append(dict(path=list(path),value_sha256=sha(canonical(expand(v['FnPtr'])))))
  rows.append(dict(id=f['def_id'],name=textname(m['name']),name_sha256=sha(canonical(expand(m['name']))),span=span,file=file['name'],source_text_sha256=sha((m['source_text'] or '').encode()),opacity=m['opacity'],body_kind=f['body'] if isinstance(f['body'],str) else 'Structured',calls=calls,function_pointer_mentions=other))
 result=dict(schema='s10-entrypoint-monomorphized-census-v1',input=pin,has_errors=x['has_errors'],charon_version=x['charon_version'],crate=t['crate_name'],options=t['options'],declarations=rows,counts=dict(declarations=len(rows),body_kinds=dict(collections.Counter(f['body_kind'] for f in rows)),call_kinds=dict(collections.Counter(c['kind'] for f in rows for c in f['calls']))),scope='Native target diagnostic; all compiler-emitted instances retained, but source-to-SBF inline correspondence and target cfg remain unproved')
 out=H/'collected'/(name+'.json');out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');print(name,result['counts'],'errors',x['has_errors'],flush=True)
