"""Build the content-addressed wide constructor packet after focused checks."""
from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent;R=E.parent.parent
obj=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def proof(attempt,names):
 p=E/attempt/'receipt.json';d=obj(p);assert d['exit_status']==0 and all('sorryAx' not in s for s in d['print_axioms'])
 return dict(receipt=str(p.relative_to(R)),receipt_sha256=sha(p),theorems=names)
f='crates/aspis-core/src/field/wide_exact.rs::WideExact::from_limbs'
row=next(r for r in obj(E.parent/'native-ledger3-20261029/NDT_LEDGER.json')['rows'] if r['function']==f)
p=dict(schema='NEI-actual-wide-constructor-v1',function=f,claim_id='NEI::WideExact::from_limbs',status='CLOSED-CONDITIONAL',route='D188_ACTUAL_WIDE_CTOR',frozen_revision=row['frozen_revision'] if 'frozen_revision' in row else '4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',source_body_sha256=row['frozen_body_sha256'],domain='All eight raw U32 words; rejection and success both included',lean_evidence=[proof('NEI_L075',['NEI_WideCtorLaw.limbs_result','NEI_WideCtorLaw.complete']),proof('NEI_L085',['NEI_WideCtorAssociation.same_result'])],native_pair=['NEI_K031','NEI_K032','NEI_wrong_wide_ctor'],remaining_inner_hypotheses=[],suspended_neb_credits_restored=[],trust_reclassification='P6/D188 retained, never removal',review=dict(path=str((E/'NEI_WIDE_CTOR_ASSOCIATION.md').relative_to(R)),sha256=sha(E/'NEI_WIDE_CTOR_ASSOCIATION.md')))
(E/'NEI_WIDE_CTOR_PACKET.json').write_text(json.dumps(p,indent=2)+'\n')
