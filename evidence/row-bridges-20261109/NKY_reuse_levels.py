from pathlib import Path
import json,lzma,hashlib,subprocess
E=Path(__file__).resolve().parent;root=E.parent.parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def read(p):
 f=root/p
 return f.read_bytes()if f.is_file()else subprocess.check_output(['git','show','HEAD:'+p],stderr=subprocess.DEVNULL)
rows=[]
for d,a,positive in [('terminal4-20261108','NKI_K001',True),('terminal4-20261108','NKI_K002',False),('terminal2-20261108','NJL_K059',True),('terminal2-20261108','NJL_K060',False)]:
 prefix='evidence/'+d+'/'+a
 raw=read(prefix+'/receipt.json');r=json.loads(raw)
 assert (r['exit_status']==0)==positive
 verified=[]
 for n,h in r.get('source_hashes',{}).items():
  candidates=[prefix+'/sources/'+n,'evidence/'+d+'/'+n]
  found=None
  for p in candidates:
   for suffix in ['', '.xz']:
    try:
     data=read(p+suffix);b=lzma.decompress(data)if suffix else data
    except (subprocess.CalledProcessError,lzma.LZMAError):continue
    if sha(b)==h:found=(p+suffix,b);break
   if found:break
  assert found,(a,n,'no retained input matching receipt hash')
  p,b=found
  verified.append(dict(path=p,sha256=h,bytes=len(b)))
 graph=json.loads(read('evidence/'+d+'/'+a+'-graph-check.json'));lock=json.loads(read('evidence/'+d+'/'+a+'-lock-check.json'));assert graph['graph_matches_frozen']and lock['unchanged']
 rows.append(dict(attempt=a,positive=positive,exit=r['exit_status'],receipt_sha256=sha(raw),sources=verified,frozen_graph=True,lock_unchanged=True))
(E/'NKY_LEVELS_REUSE.json').write_text(json.dumps(dict(status='IMMUTABLE_INPUTS_REVALIDATED_NO_UNCHANGED_RERUN',rows=rows),indent=1)+'\n')
print('four inherited levels/child native receipts and every source hash checked')
