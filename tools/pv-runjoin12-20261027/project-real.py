"""Candidate partial extraction: ONLY three generated FnOnce shim bodies opaque.

No target/body operation is rewritten. Acceptance requires a Lean theorem for
all implementations of the opaque shims; this script does NOT establish that
they are unused or identify a shipped Records dictionary.
"""
from pathlib import Path
import copy,hashlib,json,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin12-20261027'
parent=E/'pv12-records-charon-12.llbc';dst=E/'pv12-records-real-opaque-shims.llbc'
cache={}
def expand(x):
 if isinstance(x,list):return [expand(v) for v in x]
 if not isinstance(x,dict):return x
 if 'HashConsedValue' in x:
  k,v=x['HashConsedValue'];v=expand(v);cache[k]=v;return {'ExpandedTy':v}
 if 'Deduplicated' in x:return {'ExpandedTy':copy.deepcopy(cache[x['Deduplicated']])}
 return {k:expand(v) for k,v in x.items()}
x=expand(json.loads(parent.read_text()));assert not x['has_errors'];before=copy.deepcopy(x)
t=x['translated'];changed=[]
for f in t['fun_decls']:
 if not f or not isinstance(f['body'],dict):continue
 body=f['body'].get('Structured',{});span=body.get('span',{}).get('data',{})
 if span.get('file_id')==19 and span.get('beg',{}).get('line')==250:
  assert f['def_id'] in [8,10,25] and f['item_meta']['name'][-1]=={'Ident':['call_once',0]}
  changed.append(dict(id=f['def_id'],name=f['item_meta']['name'],body_span=body['span'],old_body_sha256=hashlib.sha256(json.dumps(f['body'],sort_keys=True).encode()).hexdigest()))
  f['body']='Opaque';f['item_meta']['opacity']='Opaque'
assert [d['id'] for d in changed]==[8,10,25]
# Exhaustive semantic-data diff allowlist; no statements/signatures/types/traits
# or source metadata other than these three opacity tags may differ.
check=copy.deepcopy(x)
for row in changed:
 i=row['id'];check['translated']['fun_decls'][i]=copy.deepcopy(before['translated']['fun_decls'][i])
assert check==before
ids={}
def pack(x):
 if isinstance(x,list):return [pack(v) for v in x]
 if not isinstance(x,dict):return x
 if 'ExpandedTy' in x:
  v=x['ExpandedTy'];key=json.dumps(v,sort_keys=True)
  if key in ids:return {'Deduplicated':ids[key]}
  idx=len(ids);ids[key]=idx;return {'HashConsedValue':[idx,pack(v)]}
 return {k:pack(v) for k,v in x.items()}
output=json.dumps(pack(x),separators=(',',':'))+'\n'
if '--check' in sys.argv:assert dst.read_text()==output
else:dst.write_text(output)
cache.clear();reloaded=expand(json.loads(output));assert reloaded==x
assert before['translated']['fun_decls'][0]==reloaded['translated']['fun_decls'][0]
receipt=dict(parent_sha256=hashlib.sha256(parent.read_bytes()).hexdigest(),input_sha256=hashlib.sha256(output.encode()).hexdigest(),changed=changed,target_function_unchanged=True,all_other_declarations_unchanged=True,classification='UNACCEPTED partial-extraction candidate; universal callback irrelevance proof required; no native source identification claimed')
(E/'real-opaque-shims-preflight.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items() if k!='changed'}))
