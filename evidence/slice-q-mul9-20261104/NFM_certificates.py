"""Expected four-part hybrid certificates. Only dot rows/edges may change."""
from pathlib import Path
import json,hashlib,copy
E=Path(__file__).resolve().parent;P=E.parent/'slice-q-mul8-20261104'
obj=lambda p:json.loads(Path(p).read_text())
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
ONE='crates/aspis-r1-cost-probe/src/fast_dots.rs::four_dots_one'
FOUR='crates/aspis-r1-cost-probe/src/fast_dots.rs::four_dots'
PARTS=['result','state','ordered_effects','native_association']
DOMAIN_MODELS={
'M31::from_le_bytes':['AspisR1.NFM_Span.scalar','AspisR1.NFI_FailurePrefixes.rejected','NEV_DotReadDomain.reached'],
'M31::reduce_u64':['AspisR1.NFE_NFC_HeadDomain.canonical','AspisR1.NFM_Single.same'],
'WideExact::from_limbs':['AspisR1.NFE_NFC_HeadDomain.canonical','AspisR1.NFM_Single.same'],
'WideExact::to_limbs':['AspisR1.NFF_ReadDomains.selected','AspisR1.NFI_InnerActual.canonical_at_cut'],
'EbyKDot::new':['AspisR1.NFI_TailTrace.emitted'],
'EbyKDot::push':['AspisR1.NFM_CallDomains.tail_counts','AspisR1.NFE_WrapperBridge.domains','AspisR1.NFI_PrivateCuts.installed'],
'EbyKDot::finish':['AspisR1.NFE_NFC_PacketDomains.finish','AspisR1.NFI_PrivateCuts.installed'],
'WideExact::add':['AspisR1.NFM_CallDomains.terminal','AspisR1.NFM_Single.domains'],
'four_dots_one':['AspisR1.NFI_WrapperDomains.reached','AspisR1.NFM_Domains.slots','AspisR1.NFM_ProductInstance.wrapper']}
def expected():
 audit=obj(E/'NFM_AUDIT.json');assert audit['status']=='PASS_COMBINED_HEADLINE_NFM' and audit['roots']==124
 native=obj(E/'NFM_NATIVE_VALIDATION.json');assert native['status']=='PASS_AD_CONTROL_WINDOWS_FRAMES' and len(native['groups'])==25
 old=obj(P/'NFI_EDGES.json');edges=copy.deepcopy(old)
 corpus=obj(E.parent/'slice-q-mul7-20261104/NFF_FROZEN.json');raw=corpus['crates/aspis-r1-cost-probe/src/fast_dots.rs'].encode()
 base=obj(E.parent/'native-ledger3-20261029/NDT_LEDGER.json');byrow={r['row']:r for r in base['rows']}
 common=dict(method='C3-BIN ruling(ad), direct hybrid native/Kani/Lean P6',parts=PARTS,frozen_revision=REV,
   native_validation=dict(path='NFM_NATIVE_VALIDATION.json',sha256=sha(E/'NFM_NATIVE_VALIDATION.json')),
   reused_native_validation=dict(path='NFM_NFI_REVALIDATION.json',sha256=sha(E/'NFM_NFI_REVALIDATION.json')),
   audit=dict(path='NFM_AUDIT.json',sha256=sha(E/'NFM_AUDIT.json')),
   primitive_laws=['AspisR1.NFM_ProductInstance.main_law','AspisR1.NFM_ProductInstance.tail_law'],
   native_product_theorems=['AspisR1.NFF_Cell.primitive_reply','AspisR1.NFF_Cell.replay','AspisR1.NFF_ProductCall.replay'],
   product_domain_table=dict(path='LPh_STUBS.md',sha256=sha(E/'LPh_STUBS.md')),
   closure_semantics='CLOSED on the stated release PacketDomain; incoming producer/caller edges remain separate obligations',
   trust='Existing P6/D188 option-A semantic transport is reclassification, never removal; SDK/std/copy/allocator/ABI/runtime/physical/source-to-ELF and security premises retained',
   callee_bridge_scope='Existing CLOSED-CONDITIONAL whole-body packets on their stated domains; unrelated generic caller rows are not promoted',
   remaining_inner_hypotheses=[],whole_native_output_hypothesis=False,private_stepby_relation_hypothesis=False,
   security_target_established=False)
 certs=[]
 for rowid in ['TX1:105','TX2:071','TX1:104','TX2:070']:
  r=byrow[rowid];a,b=r['frozen_body_byte_range'];assert hashlib.sha256(raw[a:b]).hexdigest()==r['frozen_body_sha256'] and hashlib.sha256(raw).hexdigest()==r['source_file_sha256']
  one=r['function']==ONE
  domain=dict(q='the actual native borrowed608-byte array' if one else 'the actual native borrowed832-byte release opening; its first608 bytes are passed to each child',g='the SAME actual borrowed29-element g argument, with NEV_DotInputs.Canonical g',slot='0<=slot<4, established by the four actual wrapper calls' if one else 'four explicit child slots0,1,2,3',upstream='Prepared/powers/prepare canonical producer and original query caller association are retained at the OPEN incoming edge; no independent successful packet is admitted')
  cert={**copy.deepcopy(common), 'id':'NFM-ad:'+rowid,'row':rowid,'function':r['function'],'source_file_sha256':r['source_file_sha256'],'source_body_sha256':r['frozen_body_sha256'],'domain':domain,
    'model_theorem':'AspisR1.NFM_ProductInstance.installed' if one else 'AspisR1.NFM_ProductInstance.wrapper',
    'state_theorems':['AspisR1.NFM_Thread.main','AspisR1.NFM_Cuts.main','AspisR1.NFM_Cuts.abort_prefix','AspisR1.NFM_Frames.sequence'] if one else ['AspisR1.NFI_WrapperTrace.erased','AspisR1.NFI_WrapperDomains.reached'],
    'native_control':['NFM_K001','NFM_K002','NFM_K097','NFM_K098'] if one else ['NFI_K067','NFI_K068','NFI_K069','NFI_K070','NFI_K071','NFI_K072','NFI_K073','NFI_K074','NFI_K099','NFI_K100','NFM_K037','NFM_K038'],
    'control_theorems':['AspisR1.NFM_Control.fixed_outer','AspisR1.NFM_Control.fixed_terms','AspisR1.NFM_Control.body_at','AspisR1.NFM_InnerControl.at_cut'] if one else ['AspisR1.NFM_Domains.slots'],
    'ordered_effects':'Same ordered reads/products/folds and three original tail calls, or the exact terminating rejected-read prefix; no suffix after abort' if one else 'Same prefix/g and four left-to-right actual child calls, retaining child abort prefixes',
    'caller_domain_theorems':['AspisR1.NFM_Domains.limb_cap','AspisR1.NFM_Domains.sums_reset','AspisR1.NFM_Span.scalar','AspisR1.NFM_Span.tail','AspisR1.NFM_Single.domains','AspisR1.NFM_CallDomains.tail_counts'] if one else ['AspisR1.NFI_WrapperDomains.reached','AspisR1.NFM_Domains.slots'],
    'closed_callee':None if one else ['TX1:105','TX2:071']}
  certs.append(cert)
 local_claims={}
 for occurrence in base['rows']:
  for obligation in occurrence['caller_domain_obligations']:
   if obligation['id'].startswith('call-domain:'):local_claims[(obligation['caller'],obligation['callee'])]=obligation['callee_claims']
 changed=[]
 for e in edges['edges']:
  if e['caller'] not in [ONE,FOUR] or e['status']=='CLOSED':continue
  assert e['status']=='OPEN'
  pruned=e['caller']==ONE and e['callee'] in ['crates/aspis-core/src/field.rs::CM31::add','crates/aspis-core/src/field.rs::M31::add','crates/aspis-core/src/field.rs::QM31::add']
  short=e['callee'].split('::',1)[1]
  models=['AspisR1.NFM_CallDomains.terminal'] if pruned else DOMAIN_MODELS[short]
  e['NFM_previous_obstacle']=e['obstacle'];e['obstacle']=None
  e['status']='CLOSED';e['classification']='CONSERVATIVE_ALTERNATIVE' if pruned else 'AD_SAME_EXECUTION_CALL'
  e['selected_target']=not pruned;e['static_resolution']='Frozen typed terminal WideExact receiver, exact emitted body and native K093/K094' if pruned else 'Frozen body/call order, actual logged arguments and same-input cut trace'
  e['model_domain_theorems']=models
  e['certificate']=dict(id='NFM-edge:'+e['obligation_id'],edge=e['edge'],status='CLOSED',kind='STATIC_UNREACHABLE' if pruned else 'HYBRID_AD_SAME_EXECUTION',frozen_revision=REV,source_body_sha256=e['source_body_sha256'],selected_callee_claims=(['NFM-ad:TX1:105','NFM-ad:TX2:071'] if e['callee']==ONE else local_claims[(e['caller'],e['callee'])]),inner_hypotheses_discharged=e['required_named_hypotheses'],hypothesis_discharge_theorems={h:models for h in e['required_named_hypotheses'] if h.endswith('.PacketDomain')},physical_discharge=dict(method='ruling(ad) native control/window substitution, not a model-only equality',native='NFM_NATIVE_VALIDATION.json',reused_native='NFM_NFI_REVALIDATION.json',model='NFM_ProductInstance.installed' if e['caller']==ONE else 'NFM_ProductInstance.wrapper',audit='NFM_AUDIT.json'),residual_hypotheses=[],trust=common['trust'])
  e['required_named_hypotheses']=[];changed.append(e['edge'])
 assert len(changed)==12
 # Every outgoing edge of the two composed functions is either selected and
 # domain-certified or a formally/native certified conservative alternative.
 assert all(e['status']=='CLOSED' for e in edges['edges'] if e['caller'] in [ONE,FOUR])
 closed=dict(schema='NFM-NDT-composed-v1',headline='AspisR1.RPx_Deployed.deployed',newly_closed=[c['row'] for c in certs],dot_rows={c['row']:dict(function=c['function'],status='CLOSED',certificate=c['id'],domain=c['domain']) for c in certs},roots=obj(P/'NFI_CLOSED.json')['roots'],retained_upstream_obligations=['query_values original caller/proof/prefix association','canonicality of SAME g from Prepared/powers/prepare out-of-slice producer','query_values observer-interface rule14 admissibility','NFG-owned headline-coherent geometry retarget'],remaining_dot_inner_hypotheses=[],security_target_established=False,cached_development_cohort=True,cold_release_replay=False)
 delta=dict(schema='NFM-additive-NFI-v1',baseline_validator='evidence/slice-q-mul8-20261104/NFI_validate.py',baseline_validator_sha256=sha(P/'NFI_validate.py'),newly_closed=closed['newly_closed'],new_count=4,newly_certified_edges=changed,new_edge_count=12,newly_certified_incoming_edges=[e for e in changed if e.startswith(FOUR+' -> ')],query_values_incoming_edge_closed=False,edge_total=257,edge_closed=sum(e['status']=='CLOSED' for e in edges['edges']),roots=closed['roots'],headline=closed['headline'],trust=common['trust'],sibling_combined_credit=False,security_target_established=False)
 return certs,edges,closed,delta
if __name__=='__main__':
 certs,edges,closed,delta=expected()
 for name,data in [('NFM_CERTIFICATES.json',certs),('NFM_EDGES.json',edges),('NFM_CLOSED.json',closed),('NFM_LEDGER_DELTA.json',delta)]: (E/name).write_text(json.dumps(data,indent=2)+'\n')
 print(json.dumps(delta))
