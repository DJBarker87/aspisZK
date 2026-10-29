"""Read-only exact source and LLBC inventory for the structured-Drop route."""
from pathlib import Path
import hashlib,json
from run import H
out={};sha=lambda b:hashlib.sha256(b).hexdigest()
for name in ['1.94.1-x86_64-unknown-linux-gnu','nightly-2026-06-01-x86_64-unknown-linux-gnu']:
 root=Path('/home/dombarker/.rustup/toolchains')/name/'lib/rustlib/src/rust/library'
 rows=[]
 for f in ['core/src/iter/range.rs','core/src/ops/range.rs','core/src/iter/traits/collect.rs','core/src/mem/mod.rs']:
  p=root/f;raw=p.read_bytes();s=raw.decode();lines=s.splitlines();hits=[i for i,l in enumerate(lines)if any(t in l for t in ['impl<T: TrustedStep> RangeIteratorImpl for ops::Range<T>','impl<A: Step> Iterator for ops::Range<A>','impl<I: Iterator> IntoIterator for I','pub struct Range<Idx>'])]
  rows.append(dict(path=str(p),sha256=sha(raw),spans=[dict(line=i+1,text='\n'.join(lines[i:i+22]))for i in hits]))
 out[name]=rows
p=H/'source-prepared-resume12/PV_B3P_SourcePrepared12.llbc';x=json.loads(p.read_text());t=x['translated'];drops=[]
def walk(v,path):
 if isinstance(v,dict):
  for k,w in v.items():
   if k.lower()=='drop':drops.append(dict(path=path+[k],statement=w))
   walk(w,path+[k])
 elif isinstance(v,list):
  for i,w in enumerate(v):walk(w,path+[i])
for f in t['fun_decls']:
 if f:
  before=len(drops);walk(f,['function',f['def_id']])
  for row in drops[before:]:row['owner']=f['item_meta']['name'];row['owner_span']=f['item_meta']['span']
out['source_prepared_llbc']=dict(path=str(p),sha256=sha(p.read_bytes()),drops=drops,source_function_names=[dict(id=f['def_id'],name=f['item_meta']['name'])for f in t['fun_decls']if f and 'qm31_sum_products3_prepared'in str(f['item_meta']['name'])])
(H/'range-source-resume13.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(dict(drop_sites=len(drops),source_prepared_llbc_sha256=sha(p.read_bytes()))))
