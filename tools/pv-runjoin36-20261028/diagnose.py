"""Read-only diagnostic of rejected LLBC, not a replacement extraction/model."""
import json,pathlib,hashlib
w=pathlib.Path('/home/dombarker/project-offloads/codex-pv-runjoin-20261026/runjoin36-extraction')
def contains(x,key):
 if isinstance(x,dict):return key in x or any(contains(v,key) for v in x.values())
 if isinstance(x,list):return any(contains(v,key) for v in x)
 return False
rows=[]
for leaf in ['SelectedMask.llbc','SelectedMask-narrow.llbc']:
 p=w/leaf;x=json.load(open(p));t=x['translated'];esc=[];drops=[]
 for f in t['fun_decls']:
  if f is None:continue
  name=f['item_meta']['name'];span=f['item_meta']['span'];q=dict(def_id=f['def_id'],name=name,span=span,body_kind=list(f['body']) if isinstance(f.get('body'),dict) else str(type(f.get('body'))))
  if contains(f['signature']['output'],'Ref'):esc.append(q)
  if contains(f.get('body'),'Drop'):drops.append(q)
 rows.append(dict(input=leaf,sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size,has_errors=x['has_errors'],function_count=len(t['fun_decls']),escaping_reference_outputs=esc,structured_drop_functions=drops,options=t['options']))
(w/'preflight-diagnostic.json').write_text(json.dumps(rows,indent=2)+'\n')
for r in rows:print(r['input'],r['function_count'],'functions;',len(r['escaping_reference_outputs']),'reference output signatures;',len(r['structured_drop_functions']),'functions with Drop')
