"""Read-only LLBC formatting call-site and reference inventory, with branch context."""
from pathlib import Path
import json,hashlib
from run import H
out=[]
for variant in ['compstdcone','partsstdcone','stdcone']:
 p=H/('PV_B3P_227_'+variant+'_resume5.llbc');x=json.loads(p.read_text())['translated'];fs={f['def_id']:f for f in x['fun_decls'] if f}
 names={i:'::'.join(a['Ident'][0]for a in f['item_meta']['name'] if 'Ident'in a)for i,f in fs.items()}
 files={f['id']:f['name']for f in x['files']};edges=[];refs=[]
 def regular(o):
  if isinstance(o,dict):
   if 'Fun'in o and isinstance(o['Fun'],dict) and 'Regular'in o['Fun']:yield o['Fun']['Regular']
   for k,v in o.items():yield from regular(v)
  elif isinstance(o,list):
   for v in o:yield from regular(v)
 def walk(o,caller,context=[]):
  if isinstance(o,dict):
   if 'kind'in o and isinstance(o['kind'],dict):
    k=o['kind']
    if 'Call'in k:
     call=k['Call']['call'];ts=list(regular(call['func']))
     for t in set(ts):edges.append(dict(caller=caller,callee=t,caller_name=names[caller],callee_name=names[t],span=o['span'],context=context,call=call))
    for t in set(regular(k.get('Assign',[]))):
     if 'fmt'in names.get(t,''):refs.append(dict(caller=caller,callee=t,caller_name=names[caller],callee_name=names[t],span=o['span'],context=context))
   for k,v in o.items():
    if k in ['If','SwitchInt','Match']:walk(v,caller,context+[dict(branch_kind=k,description=str(v)[:300])])
    else:walk(v,caller,context)
  elif isinstance(o,list):
   for v in o:walk(v,caller,context)
 for i,f in fs.items():walk(f.get('body'),i)
 interesting=[e for e in edges if any(t in e['callee_name']for t in ['fmt','panic','unwrap_failed','slice_index_fail','copy_from_slice']) or 'fmt'in e['caller_name']]
 out.append(dict(variant=variant,llbc_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),files=files,names=names,call_edges=edges,format_and_panic_edges=interesting,format_references=refs))
(H/'format227-llbc-resume7.json').write_text(json.dumps(out,indent=2)+'\n')
for r in out:
 print(r['variant'])
 for e in r['format_and_panic_edges']:print(e['caller'],e['caller_name'],'->',e['callee'],e['callee_name'],e['span']['data'],len(e['context']))
 print('references',r['format_references'])
