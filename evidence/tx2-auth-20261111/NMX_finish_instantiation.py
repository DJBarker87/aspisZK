from pathlib import Path
from collections import Counter
import hashlib,json,lzma
p=Path(__file__).resolve().parent
rows=[json.loads(l) for l in (p/'NMX_ATTEMPTS.jsonl').read_text().splitlines()]
ids=[1065,1067,1068,1069,1070,1071]
gates=[]
for i in ids:
 r=next(r for r in rows if r.get('attempt')=='NMX_L'+str(i) and r.get('kind') in ['lean','audit','inspect'])
 assert r['exit_status']==0 and r.get('axioms_accepted',True)
 gates.append({k:r.get(k) for k in ['attempt','module','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','source_hashes','print_axioms']})
selection=json.loads((p/'NMX_233_AUDIT_SELECTION.json').read_text())
for m,x in selection['modules'].items():
 assert hashlib.sha256((p/(m+'.lean')).read_bytes()).hexdigest()==x['source_sha256']
pins=json.loads(lzma.decompress((p/'NMX_233_CLOSURE_PINS.json.xz').read_bytes()))
assert hashlib.sha256(lzma.decompress((p/'NMX_233_CLOSURE_PINS.json.xz').read_bytes())).hexdigest()==(p/'NMX_233_CLOSURE_PINS.json.sha256').read_text().strip()
assert all('/NMX_R3_canonical_objects/' in x['path'] for x in pins['objects'] if x['module'].startswith('RSL_'))
x=dict(status='PASS for frozen operational instantiation; not a full233 candidate',targets=['NMX_R3_Instantiated233.native','NMX_R3_Instantiated233.represented'],frozen_targets=['NMX_R2_NativeCanonical.fold','NMX_R2_RepresentedFold.fold'],library='LIBB_PoolLib.library / deployed; module8 supplied instance',children={'TX2:217':'NMX_R3_LaneInstance.packet from NMX_R3_DecoderFold.root','TX2:234':'NMX_R3_RegistryRoot.root'},own_current_modules=3,raw_own_theorems=selection['theorems'],raw_group='proof311',standard_axioms=['propext','Classical.choice','Quot.sound'],gates=gates,raw_audit='NMX_L1069 / NMX_audit/proof311',export='NMX_233_EXPORT.json',closure_pins='NMX_233_CLOSURE_PINS.json.xz',readiness='NMX_242_241_READINESS.md',remaining='NMX_REV2_REMAINING items1-3; no child schema/library identity premise remains')
(p/'NMX_233_VALIDATION.json').write_text(json.dumps(x,indent=1)+'\n')
c=Counter(r.get('kind') for r in rows);formal=sum(c[k] for k in ['lean','link','audit','inspect'])
(p/'NMX_RESUMPTION_COUNTS.json').write_text(json.dumps(dict(prior_formal=626,current_formal=formal,resumption_formal=formal-626,formal_ceiling=826,formal_remaining=826-formal,extraction_total=c['extract'],extraction_resumption=0,kani_total=c['kani'],kani_resumption=0,stop_reason='requested234 candidate, frozen233 instantiation and242/241 readiness handoff delivered; not a budget stop',credit='ledger only'),indent=1)+'\n')
f=p/'NMX_CLOSED.json';v=json.loads(f.read_text());v['rows'][0]['validation']='NMX_233_VALIDATION.json: twelve own new-root raw ax2 PASS; L1070 focused combined import PASS; L1071 retained closure PASS';v['frozen_233_instantiation_validation']='NMX_233_VALIDATION.json';v['resumption_counts']='NMX_RESUMPTION_COUNTS.json';v['current_candidate_packet_complete']=True;v['security_target_established']=False;f.write_text(json.dumps(v,indent=2)+'\n')
print(json.dumps(dict(status='PASS',formal=formal,resumption_formal=formal-626,remaining=826-formal,loaded_modules=pins['modules'])))
