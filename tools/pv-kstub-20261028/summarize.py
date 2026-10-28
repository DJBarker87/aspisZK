"""Rebuild the per-harness/window comparison table from retained receipts."""
from pathlib import Path
import json,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-kstub-20261028';P=R/'evidence/pv-relink-20261028'
plans=json.loads((E/'plans.json').read_text());results=[json.loads(f.read_text()) for f in sorted(E.glob('K*-result.json'))]
rows=[]
for row in ['V178','V179','V182','V195','V233']:
 hs=[]
 for p in plans:
  if p['row']!=row:continue
  rs=[r for r in results if r['harness']==p['harness'] and r.get('window')==p.get('window')]
  pos=next((r for r in reversed(rs) if not r['negative_control']),None);neg=next((r for r in reversed(rs) if r['negative_control']),None)
  hs.append(dict(**p,attempts=rs,positive=pos,negative_control=neg,confirmed=bool(pos and neg and pos['status']=='PASS' and neg['status']=='FAIL')))
 finding=any(x['positive'] and x['positive']['status']=='FAIL' or x['negative_control'] and x['negative_control']['status']=='PASS' for x in hs)
 complete=all(x['confirmed'] for x in hs)
 status='finding' if finding else 'stubbed Kani confirmed' if complete else 'stubbed Kani unconfirmed (timeouts)' if any(x['positive'] and x['positive']['status']=='TIMEOUT' or x['negative_control'] and x['negative_control']['status']=='TIMEOUT' for x in hs) else 'pending'
 rows.append(dict(row=row,status=status,harnesses=hs,structural_evidence='structural (K-1 substitute)',structural_binding=str((P/(row+'-binding.json')).relative_to(R)),native_finite_validation={'V178':774256,'V179':2224136,'V182':5679337,'V195':108309,'V233':66064}[row],comparison='disagreement requiring joint-stream finding' if finding else 'no completed result disagrees; pending/TIMEOUT gives no new credit',scope='Original bounded candidate value/native-link scope; allocator/world, source-image, compiler and deployment residuals retained'))
(E/'table.json').write_text(json.dumps(dict(base='6d4350e42c6181924b80483f19fa6ccac5c3b4a7',patch_sha256='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67',rows=rows,target='not yet established',endpoint_premises_removed=0,endpoint_premises_added=0,trust_items=['entropy_law','entropy_kernel','observation']),indent=2)+'\n')
for r in rows:print(r['row'],r['status'])
