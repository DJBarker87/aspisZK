from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent;R=E.parent.parent
obj=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
from NEI_field_validate import FUNCTIONS,OPS
base=obj(E.parent/'native-ledger3-20261029/NDT_LEDGER.json')
def proof(module,names):
 choices=[];source=E/(module+'.lean');full=[module+'.'+n for n in names]
 for p in E.glob('NEI_L[0-9][0-9][0-9]/receipt.json'):
  d=obj(p)
  if d['module']!=module or d['exit_status']!=0 or d['source_hashes'].get('NEI_generated/'+module+'.lean')!=sha(source):continue
  if all(any(a.startswith("'"+n+"' ") and 'sorryAx' not in a for a in d['print_axioms']) for n in full):choices.append(p)
 assert choices,module
 p=sorted(choices)[-1];return dict(receipt=str(p.relative_to(R)),receipt_sha256=sha(p),theorems=full)
packets=[]
for function,(tag,fn,kind,args) in zip(FUNCTIONS,OPS):
 row=next(r for r in base['rows'] if r['function']==function);module={'word':'NEI_FieldScalar','cm':'NEI_FieldCM','qm':'NEI_FieldQM','wide':'NEI_FieldWide'}[kind];lemma={'m_reduce':'m_reduce_u64'}.get(tag,tag)
 required=[module+'.'+lemma,'NEI_FieldFrames.'+tag,'NEI_FieldFrames.widen']
 packets.append(dict(schema='NEI-actual-field-v1',function=function,tag=tag,claim_id='NEI::field::'+tag,status='CLOSED-CONDITIONAL',route='D188_ACTUAL_IMMUTABLE_FIELD',frozen_revision=base['frozen_revision'],source_body_sha256=row['frozen_body_sha256'],domain='All typed field carriers; complete Result fidelity. Canonical mathematical laws retain their existing model domains.',lean_evidence=[proof(module,[lemma]),proof('NEI_FieldFrames',[tag,'widen']),proof('NEI_FieldCarriers',['fromtoC','tofromC','bindC','fromtoQ','tofromQ','bindQ','fromtoE','tofromE','bindE'])],required_theorems=required,new_kani_credits=[],suspended_neb_credits_restored=[],remaining_inner_hypotheses=[],review=dict(path=str((E/'NEI_FIELD_ASSOCIATION.md').relative_to(R)),sha256=sha(E/'NEI_FIELD_ASSOCIATION.md')),trust_reclassification='P6/D188 retained, never removal'))
(E/'NEI_FIELD_PACKETS.json').write_text(json.dumps(packets,indent=2)+'\n')
