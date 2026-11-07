"""Read-only generated-source preflight; never unfolds a recurrence or theorem."""
from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent;G=E/'NMC_generated'
mods=json.loads((E/'NMC_SLOT_ORDER.json').read_text());assert len(mods)==33
rows=json.loads((E/'NMC_CUT_TABLE.json').read_text())['cuts']
expected={r['occurrence']for r in rows}-{'low_callback','high_callback','rootTry','rootUnwrap'}|{'rootCopy'}
assert {m.removeprefix('NMC_SlotFrame_')for m in mods[1:]}==expected
pins=[]
for m in mods:
 p=G/(m+'.lean');s=p.read_text()
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',s)
 assert 'maxHeartbeats'not in s and 'maxRecDepth'not in s
 if m!='NMC_AllSlotFrame':
  site=m.removeprefix('NMC_SlotFrame_')
  assert 's.next=.'+site in s and '#print axioms frame_'+site in s
 pins.append(dict(module=m,sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
x=dict(status='PASS_SOURCE_MANIFEST_ONLY',source_modules=33,occurrence_schemas=35,pins=pins)
(E/'NMC_SLOT_PREFLIGHT.json').write_text(json.dumps(x,indent=2)+'\n')
print(json.dumps(dict(status=x['status'],modules=33,schemas=35)))
