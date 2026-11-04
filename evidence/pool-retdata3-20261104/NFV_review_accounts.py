from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent
rows=[]
for kind in ['meta','info']:
 for index in range(6):
  for control in ['positive','negative']:
   matches=[]
   for p in E.glob('NFV_K*-shape.json'):
    d=json.loads(p.read_text())
    if d.get('kind')==kind and d.get('index')==index and d.get('control')==control and d.get('unwind')==337:matches.append(p)
   assert len(matches)==1,(kind,index,control,matches)
   p=matches[0];a=p.name.split('-shape')[0];r=json.loads((E/a/'receipt.json').read_text());s=(E/a/'stdout.log').read_text()
   rows.append(dict(kind=kind,index=index,control=control,attempt=a,exit=r['exit_status'],timeout='timed out' in s.lower(),unwind_incomplete='unwinding assertion' in s,source_sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
assert all(r['timeout'] and not r['unwind_incomplete'] for r in rows)
splits=[]
for a in ['NFV_K003','NFV_K004','NFV_K005','NFV_K006','NFV_K007','NFV_K035','NFV_K036','NFV_K037']:
 p=E/a/'receipt.json';assert p.exists(),('split not terminal',a)
 r=json.loads(p.read_text());s=(E/a/'stdout.log').read_text();splits.append(dict(attempt=a,exit=r['exit_status'],timeout='timed out' in s.lower(),unwind_incomplete='unwinding assertion' in s))
assert all(r['timeout'] and not r['unwind_incomplete'] for r in splits)
facts=[('NFO_K057','constructor',0),('NFO_K058','constructor corruption',1),('NFR_K004','flags',0),('NFR_K005','flags corruption',1),('NFR_K006','lengths and appended metadata key',0),('NFR_K007','appended metadata corruption',1),('NFV_K008','inserted AccountInfo key6',0),('NFV_K009','inserted AccountInfo key corruption',1)]
for a,label,status in facts:
 root=E if a.startswith('NFV') else E.parent/('pool-retdata-20261104' if a.startswith('NFO') else 'pool-retdata2-20261104')
 r=json.loads((root/a/'receipt.json').read_text());s=(root/a/'stdout.log').read_text();assert r['exit_status']==status and 'timed out' not in s.lower() and 'unwinding assertion' not in s,(a,label)
out=dict(status='CLOSED-BY-RECLASSIFICATION under ruling(af)(3)',matrix=rows,splits=splits,native_facts=[dict(attempt=a,fact=f,exit=x) for a,f,x in facts],copy_patch_sha256='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67',prescribed_meta_bound='6*34+1=205; K001 incomplete at other reached AccountInfo reallocation',complete_reached_bound='max(6*34,7*48)+1=337; layouts K010 with failing K011 control',retained_trust='std/allocator Vec push/insert preservation and shifted program element, P6/D188 option A; RECLASSIFICATION not removal',new_trust_rows=[],native_copy_pass_credit=False,shipped_bug_claim=False,scope='account construction/key ordering only; caller admission/data-state role association remains B')
(E/'NFV_AF_CERTIFICATE.json').write_text(json.dumps(out,indent=1)+'\n')
print(out['status'],len(rows),'matrix results;',len(splits),'strict split results')
