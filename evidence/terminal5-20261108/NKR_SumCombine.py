"""Combine only not-yet-PASS218 helpers; preserve every original as evidence."""
from pathlib import Path
import hashlib,json,re
E=Path(__file__).resolve().parent
names=['NKR_SumCollectMeaning','NKR_SumLookupCertificate','NKR_SumRegroup','NKR_SumTensorAlgebra','NKR_SumLegacyRows','NKR_SumIntervals','NKR_SumTagPartition','NKR_SumTagPermutation','NKR_SumTagAssociation','NKR_SumScratchCoordinates','NKR_SumCopyTail','NKR_SumCopyCuts','NKR_SumCopyInvocation']
receipts=[json.loads(p.read_text()) for p in E.glob('NKR_L*/receipt.json')]
imports=[];bodies=[];pins=[]
for name in names:
 p=E/(name+'.lean');raw=p.read_text();sha=hashlib.sha256(p.read_bytes()).hexdigest()
 assert not any(r.get('exit_status')==0 and r.get('source_hashes',{}).get(p.name)==sha for r in receipts),'PASS owner must remain imported:'+name
 for imp in re.findall(r'^import ([\w.]+)',raw,re.M):
  if imp not in names and imp not in imports:imports.append(imp)
 body=re.sub(r'^import [\w.]+\n','',raw,flags=re.M)
 bodies.append('/- Original helper '+p.name+'; retained source SHA256 '+sha+' -/\n'+body)
 pins.append(dict(source=p.name,sha256=sha,bytes=p.stat().st_size,merged=True,individual_current_pass=False))
text=''.join('import '+imp+'\n' for imp in imports)+'\n'+'\n'.join(bodies)
out=E/'NKR_SumCopyAlgebraCombined.lean';out.write_text(text)
(E/'NKR_SumCombine_PROVENANCE.json').write_text(json.dumps(dict(target=out.name,sha256=hashlib.sha256(out.read_bytes()).hexdigest(),bytes=out.stat().st_size,imports=imports,inputs=pins,policy='Only uncompiled/current-not-PASS helpers; namespaces and names unchanged; originals retained; no caps/heartbeat changes'),indent=2))
print('combined13uncompiledhelpers; '+str(out.stat().st_size)+'bytes; externalimports'+str(len(imports)))
