from pathlib import Path
import json,hashlib,shutil
D=Path('/home/dombarker/project-offloads/codex-pv-extract-20261027');rows=[]
def names(n):return '::'.join(x['Ident'][0] if 'Ident' in x else '<impl>' for x in n)
for i,r in enumerate(json.loads((D/'inventory-inputs.json').read_text())):
 p=Path(r['llbc']); row=dict(r)
 if not p.exists():row['missing']=True;rows.append(row);continue
 raw=p.read_bytes(); data=json.loads(raw)['translated']; intern={}
 def gather(x):
  if isinstance(x,dict):
   if 'HashConsedValue' in x:intern[x['HashConsedValue'][0]]=x['HashConsedValue'][1]
   for v in x.values():gather(v)
  elif isinstance(x,list):
   for v in x:gather(v)
 gather(data)
 def un(x):
  if isinstance(x,dict):
   if 'Deduplicated' in x:return un(intern[x['Deduplicated']])
   if 'HashConsedValue' in x:return un(x['HashConsedValue'][1])
   return {k:un(v) for k,v in x.items()}
  if isinstance(x,list):return [un(v) for v in x]
  return x
 def refs(x):
  if isinstance(x,dict):return 'Ref' in x or any(refs(v) for v in x.values())
  return isinstance(x,list) and any(refs(v) for v in x)
 files={f['id']:f for f in data['files']}
 row.update(sha256=hashlib.sha256(raw).hexdigest(),size=len(raw),options=data['options'],reference_outputs=[],roots=[])
 for f in data['fun_decls']:
  if f is None:continue
  m=f['item_meta'];span=m['span']['data']; out=un(f['signature']['output']); entry=dict(id=f['def_id'],name=names(m['name']),file=files[span['file_id']]['name'],line=span['beg']['line'],output=out,body_kind=list(f['body']) if isinstance(f['body'],dict) else f['body'],source=m['source_text'])
  if refs(out):row['reference_outputs'].append(entry)
  if m['is_local'] and m['source_text']:row['roots'].append(entry)
 out=D/'inputs'/str(i);out.mkdir(parents=True,exist_ok=True);shutil.copy2(p,out/p.name); row['own_llbc']=str(out/p.name)
 rows.append(row)
(D/'inventory-llbc.json').write_text(json.dumps(rows,indent=2));print(len(rows))
