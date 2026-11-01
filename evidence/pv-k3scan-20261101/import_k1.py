import json,pathlib,subprocess,hashlib,re,copy
E=pathlib.Path(__file__).resolve().parent;rs=json.loads((E/'RECOVERED.json').read_text());s=json.loads((E/'inputs/k1-scan.json').read_text());idx=json.loads((E/'SOURCE_INDEX.json').read_text());B=E/'blobs'
for i,c in enumerate(s['passes']):
 matches=[x for x in rs if x['path']==c['receipt'] and ('k1_index' not in x or x['k1_index']==i)]
 if matches:x=matches[0]
 else:
  b=subprocess.check_output(['git','show',c['receipt_blob']]);r=json.loads(b);h=hashlib.sha256(b).hexdigest();(B/(h+'.json')).write_bytes(b)
  x=dict(branch=c['refs'][0],revision=s.get('heads',{}).get(c['refs'][0]),path=c['receipt'],sha256=h,receipt=r);rs.append(x)
 if isinstance(x['receipt'],list):
  x['aggregate_receipt_sha256']=x['sha256'];x['receipt']=next((v for v in x['receipt'] if isinstance(v,dict) and v.get('harness')==c['harness']),{})
 x.update(k1_index=i,ledger_rows=c['ledger_rows'],historical_harness=c['harness'],k1_status=c['status'],k1_use=c['evidence_use'],historical_command=c['command'],historical_source_revision=c['source_revision'],historical_refs=c['refs'])
 # Add known original Rust map from historical receipt; preserve scalar pins too.
 r=x['receipt'];hh=x.get('recorded_rust_hashes',{})
 def visit(d):
  if isinstance(d,dict):
   for k,v in d.items():
    h=v.get('sha256') if isinstance(v,dict) else v
    if k.endswith(('.rs','.rs.txt')) and isinstance(h,str) and len(h)==64:hh[k]=h
    if isinstance(v,(dict,list)):visit(v)
  elif isinstance(d,list):
   for v in d:visit(v)
 visit(r)
 if isinstance(r,dict) and isinstance(r.get('source_sha256'),str):hh['receipt-pinned-source.rs']=r['source_sha256']
 x['recorded_rust_hashes']=hh
# source pins for original and relocated K1 diagnostic inputs; never claim the latter byte equals original automatically
bind=json.loads((E/'inputs/k1-d347-source-bindings.json').read_text())
request={}
for b in bind:
 for f in b['files']:
  if f['path'].endswith(('.rs','.rs.txt')) and f['sha256'] not in idx:request[f['path']]=f['sha256']
for x in rs:
 for n,h in x.get('recorded_rust_hashes',{}).items():
  if h not in idx and n.startswith('/home/dombarker/'):request[n]=h
(E/'HOST_SOURCE_REQUEST.json').write_text(json.dumps(request,indent=2)+'\n');(E/'RECOVERED.json').write_text(json.dumps(rs,indent=2)+'\n');print('receipts',len(rs),'host requests',len(request))
