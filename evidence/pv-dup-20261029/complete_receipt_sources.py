"""Complete source-file names using archived compiler snapshots; preserve binding qualifications."""
from pathlib import Path
import json,subprocess,hashlib
B=Path(__file__).resolve().parent;rev='e45a05e2626fd85f9e14ca4faf2dee378470c765'
get=lambda p:subprocess.check_output(['git','show',rev+':'+p])
s=json.load(open(B/'SOURCES.json'));oldgaps=json.load(open(B/'SOURCE-GAPS.json'));seed=json.load(open(B/'source-seeds.json'));records={}
for m,a,root in [('NBD_DigestInduction','NBD_L004','native-tx2b-20261027'),('NBH_Exact','NBH_L021','native-tx2d-20261027'),('NCV_CastRef.Funs','NCV_L024','native-decref-20261028'),('NCV_Reference.Funs','NCV_L003','native-decref-20261028')]:
 receipt=f'evidence/{root}/{a}/receipt.json';d=json.loads(get(receipt));assert d['exit_status']==0
 src=d['sources'][0];p=f'evidence/{root}/{a}/sources/{src}';raw=get(p);sha=hashlib.sha256(raw).hexdigest();assert sha==d['source_hashes'][src]
 s[m].update(source=p,revision=rev,sha256=sha,basis=receipt,qualification='archived successful compiler source snapshot; READY object is retained through NDJ cache, whose source field is null; no new object/source binding claim')
 records[m]={'receipt_path':receipt,'receipt':d,'snapshot_path':p,'sha256':sha}
for m in oldgaps:
 if m.startswith('Aeneas.'):
  e=seed.get(m)
  if e:s[m].update(e,qualification='historical library source location from EJR metadata; source path may no longer exist; no source reconstruction and no object authority change')
(B/'SOURCES-COMPLETED.json').write_text(json.dumps(s,indent=2)+'\n')
(B/'archived-source-receipts.json').write_text(json.dumps(records,indent=2)+'\n')
missing=[m for m,x in s.items() if not x.get('source')];assert not missing,missing
print('All',len(s),'providers have source file names; qualifications preserved')
