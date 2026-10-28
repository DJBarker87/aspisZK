"""Record explicit public import edges; preserve the initial failed plan."""
from pathlib import Path
import json,lzma,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin32-20261028';x=json.loads((E/'focused-resolution.json').read_text());src=json.loads((E/'focused-project-sources.json').read_text());old=json.loads((E/'build-plan.json').read_text())
(E/'build-plan-initial.json').write_text(json.dumps(old,indent=2)+'\n')
seen=set();active=set();order=[]
def visit(m):
 if m not in src or m in seen:return
 assert m not in active,m
 active.add(m)
 for d in x['resolved'][m]['imports']:visit(d)
 active.remove(m);seen.add(m);order.append(m)
for m in src:visit(m)
order.remove('R1Z.PV_RunJoin_EndpointAudit20');assert order[:40]==old['order'][:40]
old.update(order=order,chunks=[order[1:40]]+[order[i:i+40] for i in range(40,len(order),40)],modules={m:x['resolved'][m] for m in src},public_import_correction=True,initial_isolated_module='QueryScanExhaustion',initial_isolated_attempt=51301,first_39_attempt=51302,added_modules=sorted(set(src)-set(old['modules'])),correction='External IR companions added after retained failed51300; public import headers now included. Same source hashes; changed verified environment.')
(E/'build-plan.json').write_text(json.dumps(old,indent=2)+'\n')
b=(E/'focused-project-sources.json').read_bytes();(E/'focused-project-sources.json.xz').write_bytes(lzma.compress(b,preset=6));(E/'focused-project-sources.json.sha256').write_text(hashlib.sha256(b).hexdigest()+'  focused-project-sources.json\n')
print('new modules',old['added_modules'],'remaining chunks',len(old['chunks'])-1)
