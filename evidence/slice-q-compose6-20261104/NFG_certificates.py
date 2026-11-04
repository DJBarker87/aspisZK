"""Four complete root recipes, not promotion of model-only dot equalities."""
from pathlib import Path
import sys,json,copy,hashlib,subprocess
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parent.parent
from NFG_proof_checks import accepted
from NFG_small_checks import check as small
from NFG_native_checks import check as native
from NFG_peer_native import check as peer
from NFG_push_source import check as push_source
from NFG_kernel_literal import check as literal
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
obj=lambda p:json.loads(p.read_text())
NEG='crates/aspis-core/src/field.rs::CM31::neg'
ZERO='crates/aspis-core/src/field.rs::QM31::is_zero'
PRIVATE='crates/aspis-r1-cost-probe/src/fast_pairing.rs::canonical::Dot::push'
PUBLIC='crates/aspis-r1-cost-probe/src/fast_pairing.rs::EbyKDot::push'
ROOTS={NEG:['TX1:009'],ZERO:['TX1:028'],PRIVATE:['TX1:111','TX2:077'],PUBLIC:['TX1:108','TX2:074']}
PROOFS=['NFG_SmallAssociation','NFG_SmallEffects','NFG_NegAssociation','NFG_ZeroAssociation','NFG_ProductOk','NFG_RawDomains','NFG_RawCoupling','NFG_PrivateWindow','NFG_PrivateTrace','NFG_PrivateNative','NFG_PublicG','NFG_PushRoot','NFG_PushComposed','NFG_DotComposed','NFG_RootsCombined']
DOMAIN={NEG:'Two canonical native u32 limbs <2147483647; exact same CM31 fields, by-value root',ZERO:'Every four raw native u32 words; exact same QM31 fields, by-value root',PRIVATE:'Two canonical private Q arrays of four u32 limbs <2147483647; arbitrary four-u64 receiver, valid unique mutable borrow',PUBLIC:'Canonical eight-word WideExact input; every raw QM31 scalar, arbitrary two four-u64 receivers and usize count, valid unique mutable borrow; both rejection branches included'}
MATH={NEG:'NFG_SmallAssociation.neg; NFG_SmallEffects.neg',ZERO:'NFG_SmallAssociation.zero; NFG_SmallEffects.zero',PRIVATE:'NFG_PushRoot.private_result/private_domains; NFG_DotComposed.private_result_state_effects',PUBLIC:'NFG_PushRoot.public_result/reject_count/reject_scalar; NFG_PublicG.source/child_domains; NFG_DotComposed.public_result_state_effects'}
LAWS={
 NEG:{'self.a.neg':'Actual M31::neg body executed by K021; checked emitted word Result NFG_NegAssociation.primitive / NFG_SmallAssociation.word; operand domain from the SAME root requires', 'self.b.neg':'Same second limb, same whole returned CM31; K021/022 and full reference/extraction association'},
 ZERO:{'self.c0.is_zero':'Actual CM31/M31 is_zero bodies executed all-raw by K019; native short-circuit, exact complete Result NFG_ZeroAssociation.result / NFG_SmallAssociation.zero','self.c1.is_zero':'Same reached second CM31 only after first true; native K019/020, full raw-word Bool and zero-test Result'},
 PRIVATE:{'a.raw':'NFF_LoggedRaw.headline binds the complete machine-operation continuation to the emitted raw Result; NFF_K019/020/068/069 raw operand/reply/order/result; all 16 primitive emitted ok/value laws NFG_ProductOk, same-log bound NFG_RawDomains.replies, actual returned array NFG_RawCoupling.native_result', 'self.sums[j].wrapping_add':'All-u64 native NFF_K021/022/068/069 arbitrary observed-coordinate update/frame; exact emitted step NFG_PrivateWindow.step; same state chain NFG_PrivateTrace.four','(raw[j]&u64::from(P)).wrapping_add':'Same all-u64 native window, same unchanged raw array; root loop 0..4 source hash and NFG_K026/027 actual Range transition; four-step kernel chain', 'u64::from':'Native same-word observation NFF_K019; exact emitted raw association and standard scalar cast on canonical u32 words'},
 PUBLIC:{'Err':'Exact rejection constructors and unchanged receiver; K029, NFG_PushRoot.reject_count/reject_scalar','canonical::Q::from_wide':'Actual child executes in K029/026; exact SAME low/high root value fields, NFG_PublicG.source and child_domains','checked_q':'Actual all-raw scalar guard executes in K029/026; exact Option/Result/error and source NFG_PublicG.check_result; valid scalars derive child domains','self.c0.push':'First actual c0 pointer, prior receiver and root operands K029; NFG_PushRoot.public_result instantiates private root cut on SAME c0','self.c1.push':'Second actual c1 pointer, prior receiver and SAME scalar K029; NFG_PushRoot.public_result instantiates private root cut on SAME c1','Ok':'Exact returned constructor and final count publication only after two reached children; K029 and NFG_PublicG.source'} }
def packet():
 p=dict(raw_coupling=dict(native='NFF_K019/020/068/069 SAME local product log and complete machine expression',model='NFF_LoggedRaw.run NFG_Primitive64.reply; NFF_LoggedRaw.headline supplies the full Result association',primitive='NFG_ProductOk.result/value and NFF_ProductCall.replay fix each product from its SAME canonical operands',natural_values='NFF_RawTypedLog.replay gives the returned array values from that SAME log; NFG_RawCoupling.native_result uses those acquired observations',residual_inner_hypotheses=[]),proofs=[accepted(m) for m in PROOFS],scalar=small(),native=native(),peer_native=peer(),source=push_source(),literal=literal(),
  primitive_stub_table_sha256=sha(E/'NFG_LPh_STUBS.md'),
  scripts={n:sha(E/n) for n in ['NFG_proof_checks.py','NFG_small_checks.py','NFG_native_checks.py','NFG_peer_native.py','NFG_push_source.py','NFG_certificates.py']},
  peer_revision=obj(E/'NFG_PEER_IMPORT.json'),peer_final=obj(E/'NFG_PEER_FINAL.json'),
  roots={root:dict(rows=rows,domain=DOMAIN[root],model=MATH[root],remaining_inner_hypotheses=[]) for root,rows in ROOTS.items()},
  top_hypotheses=['RootPacketDomain','RootPhysicalInterpretation','NativeContractSemanticTransport','RustABIAndStdRealisation'],
  transport='Owner option A: P6/D188 reclassification, not assumption removal. Pure-model state/effects do not assert empty native panic I/O.',
  no_credit=['four_dots_one','four_dots','query_values','query_loop','generic CM31::inv_with','inverse G windows'],
  inherited_qualification='NFB source-validator geometry count retained. NEW/NFB combined Phase-owner conflict against RPx remains; no combined headline release theorem claimed.')
 return p

def expected(base,p):
 rows=[]
 for r in base['rows']:
  root=r['function']
  if root not in ROOTS:continue
  assert r['row'] in ROOTS[root]
  frozen=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+r['source_file']],cwd=R)
  a,b=r['frozen_body_byte_range'];assert hashlib.sha256(frozen[a:b]).hexdigest()==r['frozen_body_sha256']
  assert {c.get('expression',c.get('syntax')) for c in r['callees']}==set(LAWS[root]),(root,'new unclassified callee')
  laws=[dict(call=c,status='CLOSED',law=LAWS[root][c.get('expression',c.get('syntax'))],typed_resolution=('M31::neg, not the inventory self-owner CM31 alternative' if root==NEG else 'CM31::is_zero with actual M31 descendants, not the inventory self-owner QM31 alternative') if root in [NEG,ZERO] else 'Exact typed frozen call site; immutable native/source/kernel association') for c in r['callees']]
  rows.append(dict(id='NFG-root:'+r['row'],row=r['row'],function=root,domain=DOMAIN[root],frozen_body_sha256=r['frozen_body_sha256'],packet_sha256=sha(E/'NFG_PACKETS.json'),call_obligations=laws,inventory_obligations=[dict(original=o,status='CLOSED',law=MATH[root]+'; native SAME root record, bounds and frames; replaces suspended historical LPn passes') for o in r['inventory_domain_obligations']],parts=['full_Result','same_carrier','returned_state','persistent_state','semantic_effects','native_association','all_reached_child_domains','frame','ordered_trace'],remaining_inner_hypotheses=[],top_hypotheses=p['top_hypotheses']))
 assert {r['row'] for r in rows}=={v for values in ROOTS.values() for v in values}
 return sorted(rows,key=lambda r:r['row'])

def edges(old,p):
 out=copy.deepcopy(old);new=[]
 for e in out['edges']:
  if e['caller']!=PUBLIC:continue
  assert e['callee'] in {PRIVATE,'crates/aspis-r1-cost-probe/src/fast_pairing.rs::canonical::Q::from_wide','crates/aspis-r1-cost-probe/src/fast_pairing.rs::checked_q'}
  assert e['status']=='OPEN'
  e.update(status='CLOSED',obstacle=None,classification='COMPOSED_CALL_SITE',selected_target=True,model_domain_theorems=['NFG_PublicG.source','NFG_PublicG.child_domains','NFG_PushRoot.public_result'],certificate=dict(id='NFG-push-call:'+e['edge'],packet_sha256=sha(E/'NFG_PACKETS.json'),parts=['packet_domain','same_arguments_Result','ordered_calls','state_effects','physical_interpretation','native_association'],residual_inner_hypotheses=[]))
  new.append(e['edge'])
 assert len(new)==3
 out['NFG_root_row_certificates']=obj(E/'NFG_CERTIFICATES.json')
 return out,new
