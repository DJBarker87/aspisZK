from pathlib import Path
import json,re,hashlib,sys
E=Path(__file__).resolve().parent;G=E/'NCV_generated'
rows=[json.loads(l) for l in (E/'NCV_ATTEMPTS.jsonl').read_text().splitlines()]
accepted={}
for x in rows:
 if x['kind']=='lean' and x['exit_status']==0 and not x['module'].endswith('Info'):
  n=x['module'];p=G/(n+'.lean');key='NCV_generated/'+n+'.lean'
  if p.exists() and hashlib.sha256(p.read_bytes()).hexdigest()==x['source_hashes'][key]:accepted[n]=x
names=sorted({m.group(1) for x in accepted.values() for line in x['print_axioms'] for m in [re.search(r"'([^']+)'",line)] if m})
s=''.join('import '+n.replace('/','.')+'\n' for n in sorted(accepted))
s+='\n-- Final focused closure/axioms audit; no frozen release replay.\n'
s+=''.join('#print axioms '+n+'\n' for n in names)
for ns in ['NCV_Reference','NCV_CastRef']:
 for fn in ['decode_master_ref','decode_checkpoint_ref','decode_lane_ref']:s+='#print axioms '+ns+'.'+fn+'\n'
(G/'NCV_Audit.lean').write_text(s)
(E/'NCV_ACCEPTED_MODULES.json').write_text(json.dumps({n:{'attempt':x['attempt'],'source_sha256':x['source_hashes']['NCV_generated/'+n+'.lean'],'axioms':x['print_axioms']} for n,x in accepted.items()},indent=2)+'\n')
print('audit imports',len(accepted),'new top theorem audits',len(names))
