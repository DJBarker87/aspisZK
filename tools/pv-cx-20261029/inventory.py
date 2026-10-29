"""Diagnostic LLBC inventory. Never promote has_errors output to accepted extraction."""
from pathlib import Path
import collections,hashlib,json,sys
p=Path(sys.argv[1]);O=Path(sys.argv[2]);O.mkdir(exist_ok=True)
raw=p.read_bytes();d=json.loads(raw);t=d['translated'];intern={}
def gather(x):
 if isinstance(x,dict):
  if 'HashConsedValue' in x:intern[x['HashConsedValue'][0]]=x['HashConsedValue'][1]
  for v in x.values():gather(v)
 elif isinstance(x,list):
  for v in x:gather(v)
gather(t)
def un(x):
 if isinstance(x,dict):
  if 'Deduplicated' in x:return un(intern[x['Deduplicated']])
  if 'HashConsedValue' in x:return un(x['HashConsedValue'][1])
  return {k:un(v) for k,v in x.items()}
 if isinstance(x,list):return [un(v) for v in x]
 return x
def name(ns):
 return '::'.join(n['Ident'][0] if 'Ident' in n else '<'+json.dumps(un(n),separators=(',',':'))+'>' for n in ns)
files={f['id']:f for f in t['files']};funcs={f['def_id']:f for f in t['fun_decls'] if f};calls=collections.defaultdict(list);terminals=[]
def span(s):
 s=(s or {}).get('data',s or {});f=files.get(s.get('file_id'),{});return dict(file=f.get('name'),beg=s.get('beg'),end=s.get('end'))
def walk(x,caller,s=None):
 if isinstance(x,dict):
  s=x.get('span',s)
  if 'Call' in x:
   c=x['Call']['call'];r=c['func'].get('Regular',{});k=r.get('kind',{}).get('Fun',{}).get('Regular')
   if k is not None:calls[k].append(dict(caller=caller,source=span(s),kind='Call'))
  if 'Drop' in x:
   k=x['Drop']['fn_ptr'].get('kind',{}).get('Fun',{}).get('Regular')
   if k is not None:calls[k].append(dict(caller=caller,source=span(s),kind='Drop',drop_kind=x['Drop'].get('kind')))
  for k in ['Abort','Assert']:
   if k in x:terminals.append(dict(caller=caller,source=span(s),kind=k,operation=un(x[k])))
  for v in x.values():walk(v,caller,s)
 elif isinstance(x,list):
  for v in x:walk(v,caller,s)
for f in funcs.values():
 if isinstance(f['body'],dict):walk(f['body'],name(f['item_meta']['name']))
def classify(n):
 if 'prove_for_proof_accounts' in n:return ['file','entropy','clock','alloc','exit/panic','pure-library'],'aggregate existing prover boundary; must link, not duplicate'
 if any(k in n for k in ['std::fs::','std::os::unix::fs::','DurableStateOnlyMaskNonceStore']):return ['file'],'filesystem or durable nonce-store boundary; lower-level effect closure not yet proved'
 if '_eprint' in n or 'stderr' in n:return ['stderr'],'path classification only'
 if '_print' in n or 'stdout' in n:return ['stdout'],'path classification only'
 if any(k in n for k in ['std::io::','read_to_string']):return ['file'],'includes standard input and std::io support; not a purity claim'
 if any(k in n for k in ['serde_json','serde::']):return ['JSON'],'includes parsing/serialization trait interface'
 if any(k in n for k in ['std::time::','Instant','SystemTime']):return ['clock'],'path classification only'
 if 'getrandom' in n:return ['entropy'],'path classification only'
 if any(k in n for k in ['panic','abort','std::process::exit']):return ['exit/panic'],'path classification only'
 if any(k in n for k in ['drop','alloc::','clone']):return ['alloc','pure-library'],'allocation/drop possibility; exact effects not established'
 return [],'UNCLASSIFIED opaque library operation; no claim of purity or absence of effects'
rows=[]
for k,f in funcs.items():
 if f['body']!='Opaque':continue
 n=name(f['item_meta']['name']);classes,note=classify(n)
 unique={json.dumps(s,sort_keys=True):s for s in calls[k]}
 rows.append(dict(llbc_fun_id=k,rust_path=n,rust_name_structured=un(f['item_meta']['name']),signature_llbc=un(f['signature']),generics_llbc=un(f['generics']),definition=span(f['item_meta'].get('span')),source_call_sites=list(unique.values()),effect_class=classes,classification_note=note,lean_external_op=None))
roots=[dict(rust_path=name(f['item_meta']['name']),body_kind=list(f['body']) if isinstance(f['body'],dict) else f['body'],source=span(f['item_meta'].get('span'))) for f in funcs.values() if f['item_meta']['is_local']]
artifact=dict(sha256=hashlib.sha256(raw).hexdigest(),bytes=len(raw),charon_version=d['charon_version'],has_errors=d['has_errors'],options=t['options'])
(O/'effect-interface.json').write_text(json.dumps(dict(status=('REJECTED Charon diagnostic' if d['has_errors'] else 'CHARON CANDIDATE ONLY') + ': no Aeneas emission or ExternalFuns class; not a completed effect interface',artifact=artifact,opaque_functions=rows,opaque_function_count=len(rows),roots=roots,nonlocal_nonopaque_functions=[dict(rust_path=name(f['item_meta']['name']),source=span(f['item_meta'].get('span'))) for f in funcs.values() if not f['item_meta']['is_local'] and isinstance(f['body'],dict)],non_external_terminals=terminals,limitations=['Any has_errors output is not accepted; this artifact has_errors is recorded above','Rust names and signatures are LLBC-level, not Lean carrier identity','Call sites are static extracted spans; not a dynamic reachability claim','Unwind and conditional drop are inventoried without adequacy credit','Empty effect_class lists are unresolved classifications; pure-library candidates never assert purity','No writer world or entropy dictionary implemented']),indent=2)+'\n')
print(json.dumps(dict(artifact=artifact['sha256'],has_errors=d['has_errors'],opaque=len(rows),roots=len(roots),calls=sum(len(x['source_call_sites']) for x in rows))))
