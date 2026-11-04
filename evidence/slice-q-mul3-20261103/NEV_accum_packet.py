"""Fail-closed actual accumulation packet; no ledger promotion here."""
from pathlib import Path
import json,hashlib,sys
sys.dont_write_bytecode=True
from NEV_accum_native import pair,PAIRS,copy_groups
from NEV_codefield_validate import validate as constructor
from NEV_prefix_validate import neb
E=Path(__file__).resolve().parent;R=E.parent.parent
obj=lambda p:json.loads(Path(p).read_text())
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
PROOFS=[('NEV_L026',['NEV_AccumulateCarriers.prepared_roundtrip','NEV_AccumulateCarriers.prepared_reverse','NEV_AccumulateCarriers.accumulator_roundtrip','NEV_AccumulateCarriers.accumulator_reverse']),('NEV_L029',['NEV_BasisRaw.inner_step','NEV_BasisRaw.inner_loop']),('NEV_L031',['NEV_BasisOuterStep.body']),('NEV_L033',['NEV_BasisOuterRaw.levels_eq']),('NEV_L035',['NEV_PushUse.association']),('NEV_L038',['NEV_BorrowMaps.weight_read']),('NEV_L039',['NEV_CtorNormalization.cohort']),('NEV_L041',['NEV_BasisProducer.total','NEV_BasisProducer.read_canonical']),('NEV_L045',['NEV_RowStep.active','NEV_RowStep.stop']),('NEV_L048',['NEV_RowLoop.association']),('NEV_L049',['NEV_AccumulatePrefix.association']),('NEV_L052',['NEV_MaskCarriers.product_words']),('NEV_L053',['NEV_MaskQM.add','NEV_MaskQM.multiply','NEV_MaskQM.normalization']),('NEV_L056',['NEV_StageWideFields.add','NEV_StageWideFields.product']),('NEV_L057',['NEV_PrimitiveBindings.product','NEV_PrimitiveBindings.product_returns','NEV_PrimitiveBindings.add','NEV_PrimitiveBindings.power']),('NEV_L059',['NEV_TailModel.association']),('NEV_L060',['NEV_AccumulateComplete.reference','NEV_AccumulateComplete.native']),('NEV_L061',['NEV_PushDomains.canonical_limb','NEV_PushDomains.reached']),('NEV_L063',['NEV_BasisCallDomains.scalar','NEV_BasisCallDomains.active_level']),('NEV_L070',['NEV_ReachedProgress.next']),('NEV_L067',['NEV_WeightDomains.read']),('NEV_L068',['NEV_AccumPacket.raw_length','NEV_AccumPacket.result_state_effects','NEV_AccumPacket.no_base_dependency'])]
def proof(label,names):
 path=E/label/'receipt.json';item=dict(receipt=str(path.relative_to(R)),receipt_sha256=sha(path),theorems=names)
 for name in names:neb.check_receipt(item,name)
 return item

def packet():
 constructors=constructor();native=[pair(*x) for x in PAIRS];copies=copy_groups()
 assert constructors['status']=='CLOSED-CONDITIONAL_AUXILIARY'
 imports=obj(E/'NEV_ACCUMULATE_IMPORT.json')
 for item in imports:
  assert sha(R/item['source'])==item['source_sha256'] and sha(R/item['destination'])==item['sha256']
 original=(R/imports[1]['source']).read_text();assert (R/imports[1]['destination']).read_text()==original.replace('NEI_AccumulateIsolated','NEV_AccumulateRaw')
 types=(E/'NEV_AccumulateRaw/Types.lean').read_text()
 assert 'instance NEV_discriminantVariant' in types and '@[discriminant isize]' not in types
 assert 'match v with | .S1 => 0#isize | .S2 => 1#isize | .D => 2#isize' in types
 pins=obj(R/'evidence/slice-q-mul2-20261101/NEI_E005/NEI_EXTRACTION_PINS.json')
 assert pins['charon_exit']==pins['exit']==0 and pins['lock_before']==pins['lock_after']
 for path,h in pins['outputs'].items():
  source=R/'evidence/slice-q-mul2-20261101'/path
  if path.endswith('FunsExternal_Template.lean'):source=Path(str(source)+'.txt')
  assert sha(source)==h
 for label,name in [('NEV_L025','Types'),('NEV_L027','FunsExternal'),('NEV_L028','Funs')]:
  receipt=obj(E/label/'receipt.json');assert receipt['exit_status']==0
  key='NEV_generated/NEV_AccumulateRaw/'+name+'.lean'
  assert sha(E/'NEV_AccumulateRaw'/(name+'.lean'))==receipt['source_hashes'][key]
 proofs=[proof(a,n) for a,n in PROOFS]
 for label,module in [('NEV_L070','NEV_ReachedProgress'),('NEV_L067','NEV_WeightDomains'),('NEV_L068','NEV_AccumPacket')]:
  assert sha(E/(module+'.lean'))==obj(E/label/'receipt.json')['source_hashes']['NEV_generated/'+module+'.lean']
 domain='Width64; independent global next<22 and local BW.terms<22; input immutable weight vector and folded value/rhs/power/rho canonical; input SAME-vector S7 phase Progress at cursor0. Raw length64, produced basis canonicality, every reached push overflow domain, intermediate field canonicality, and unchanged weights are derived. No child or final successful result is a premise.'
 return dict(claim_id='NEV::accumulate',function='crates/aspis-r1-cost-probe/src/verifier.rs::accumulate_batched_with_node',status='CLOSED-CONDITIONAL_LOCAL_PENDING_COMPOSITION',frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',domain=domain,lean_evidence=proofs,native_pairs=native,copy_controls=copies,auxiliary_constructor=constructors,reused_actual_extraction='NEI_E005',remaining_inner_hypotheses=[],parts=['result','state','ordered_effects','native_association'],trust='P6/D188 semantic transport option A retained, reclassification never removal; source/ABI/compiler/library/allocator/runtime/artifact qualifications retained',composed_rows_closed=[])
if __name__=='__main__':
 result=packet();(E/'NEV_ACCUM_PACKET.json').write_text(json.dumps(result,indent=2)+'\n');print(result['status'])
