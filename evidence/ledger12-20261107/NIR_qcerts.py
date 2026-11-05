from pathlib import Path
import json,subprocess,hashlib
E=Path(__file__).resolve().parent;R=E.parents[1]
p='evidence/slice-q-accum-20261104/NFS_CLOSED.json';seen=set();records={};pins=[]
while p and p not in seen:
 seen.add(p);raw=subprocess.check_output(['git','show','HEAD:'+p]);d=json.loads(raw);pins.append(dict(path=p,sha256=hashlib.sha256(raw).hexdigest()))
 certs=d.get('certificates',[])
 if isinstance(certs,dict):certs=list(certs.values())
 rowinfo=d.get('rows',{})
 if not isinstance(rowinfo,dict):rowinfo={r['row']:r for r in rowinfo if isinstance(r,dict)and'row'in r}
 for rid,info in rowinfo.items():
  if rid in records:continue
  cid=info.get('certificate')
  c=next((c for c in certs if c.get('id')==cid),None)
  if c and ('CLOSED'in str(info.get('status',''))or rid in d.get('newly_closed',[])):records[rid]=dict(source=p,packet=c)
 baseline=d.get('baseline',{});p=baseline.get('path')if isinstance(baseline,dict)else None
(E/'NIR_Q_CERTIFICATES.json').write_text(json.dumps(dict(pins=pins,rows=records),indent=1)+'\n');print('NIR Q chain',len(seen),'packets',len(records))
