from pathlib import Path
import hashlib,json
B=Path(__file__).resolve().parent
p=B/'XRe_no_copied_release_candidate_tx1.llbc';j=json.loads(p.read_text());table={}
def collect(x):
 if isinstance(x,dict):
  if list(x)==['HashConsedValue']:table[x['HashConsedValue'][0]]=x['HashConsedValue'][1]
  for v in x.values():collect(v)
 elif isinstance(x,list):
  for v in x:collect(v)
collect(j)
def expand(x):
 if isinstance(x,dict):
  if list(x)==['Deduplicated']:return expand(table[x['Deduplicated']])
  if list(x)==['HashConsedValue']:return expand(x['HashConsedValue'][1])
  return {k:expand(v) for k,v in x.items()}
 if isinstance(x,list):return [expand(v) for v in x]
 return x
def sha(x):return hashlib.sha256(json.dumps(x,sort_keys=True).encode()).hexdigest()
rows=[]
for f in j['translated']['fun_decls']:
 if f:
  m=expand(f['item_meta']);name=m['name'];rows.append(dict(id=f['def_id'],idents='::'.join(n['Ident'][0] for n in name if 'Ident' in n),full_name_sha256=sha(name),source_span=m['span'],body='Opaque' if f['body']=='Opaque' else 'Present',body_sha256=sha(expand(f['body']))))
(B/'XRe_llbc_inventory.json').write_text(json.dumps(dict(artifact_sha256=hashlib.file_digest(p.open('rb'),'sha256').hexdigest(),bytes=p.stat().st_size,has_errors=j['has_errors'],function_count=len(rows),type_count=len(j['translated']['type_decls']),functions=rows),indent=2)+'\n')
print('functions',len(rows),'opaque_release_names')
for row in rows:
 if row['body']=='Opaque' and row['idents'].startswith('aspis_r1_cost_probe'):print(row['id'],row['idents'])
