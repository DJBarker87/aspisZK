"""Content-address only specifically reviewed, current successful model proofs."""
from pathlib import Path
import hashlib,json
E=Path(__file__).resolve().parent;R=E.parent.parent
obj=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
from NEI_dot_finish_validate import FUNCTIONS,PAIRS
COMMON={'NEI_DotReduction':['constant_cast','same','value'],'NEI_ReduceRefLaw':['same','actual_reference','frame'],'NEI_DotFinishFrames':['reduce','limbs','dot','outer']}
SPEC=[{}, {'NEI_DotFinishAssociation':['limbs']}, {'NEI_DotFinishAssociation':['finish'],'NEI_DotFinishValues':['source']}, {'NEI_EbyFinishAssociation':['ctor_unwrap','same'],'NEI_PublicDotFinishValues':['source'],'NEI_WideCtorAssociation':['same_result']}]
def proof(module,names):
 source=E/(module+'.lean');choices=[]
 for p in E.glob('NEI_L[0-9][0-9][0-9]/receipt.json'):
  d=obj(p)
  if d['module']!=module or d['exit_status']!=0 or d['source_hashes'].get('NEI_generated/'+module+'.lean')!=sha(source):continue
  full=[module+'.'+n for n in names]
  if all(any(s.startswith("'"+n+"' ") and 'sorryAx' not in s for s in d['print_axioms']) for n in full):choices.append(p)
 assert choices,('no current successful proof',module)
 p=sorted(choices)[-1];return dict(receipt=str(p.relative_to(R)),receipt_sha256=sha(p),theorems=full)
base=obj(E.parent/'native-ledger3-20261029/NDT_LEDGER.json');packets=[]
for function,extra in zip(FUNCTIONS,SPEC):
 row=next(r for r in base['rows'] if r['function']==function)
 packets.append(dict(schema='NEI-actual-dot-finisher-v1',function=function,claim_id='NEI::'+function.split('rs::')[1],status='CLOSED-CONDITIONAL',route='D188_ACTUAL_DOT_FINISH',frozen_revision=base['frozen_revision'],source_body_sha256=row['frozen_body_sha256'],domain='All valid typed inputs; raw words unrestricted; count unrestricted',lean_evidence=[proof(m,n) for m,n in {**COMMON,**extra}.items()],native_pair=PAIRS[function],remaining_inner_hypotheses=[],suspended_neb_credits_restored=[],trust_reclassification='P6/D188 retained, never removal',review=dict(path=str((E/'NEI_DOT_FINISH_ASSOCIATION.md').relative_to(R)),sha256=sha(E/'NEI_DOT_FINISH_ASSOCIATION.md'))))
(E/'NEI_DOT_FINISH_PACKETS.json').write_text(json.dumps(packets,indent=2)+'\n')
