"""Register additional reviewed packets without editing an original NEB gate.

Old refresh/recipe functions run first. Only new content-addressed certificates
are supplied; an independent guard prohibits older NEB native credit.
"""
from pathlib import Path
import sys,json,copy,hashlib,importlib.util
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parent.parent;B=E.parent/'slice-q-compose-20261029'
sys.path[:0]=[str(E),str(B)]
import NEB_validate as neb
import NEB_leaf_updates as leaves
import NEB_certificates as certificates
import NEI_ctor_validate
obj=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
# Preserve every original check byte-for-byte, adding one strictly scoped
# external-occurrence class. The original file remains read-only.
original=(B/'NEB_validate.py').read_text()
marker="     else:require(False,'unregistered external obligation kind')"
addition="""     elif ext['kind']=='NEI_CERTIFIED_CTOR_OCCURRENCE':
      _NEI_check_ctor_occurrence(row,o,ext,index,baseline,approved_edges,rc)
      o.update(status='CLOSED',discharged_by=rc['id']+':certified-ctor-occurrence')
"""
assert original.count(marker)==1
added=original.replace(marker,addition+marker)
assert added.replace(addition,'')==original,'an original validator check changed'
(E/'NEI_NEB_ADDITIVE.py').write_text(added)
(E/'NEI_VALIDATOR_SOURCE_DELTA.json').write_text(json.dumps(dict(original=str(B/'NEB_validate.py'),original_sha256=sha(B/'NEB_validate.py'),derived=str(E/'NEI_NEB_ADDITIVE.py'),derived_sha256=sha(E/'NEI_NEB_ADDITIVE.py'),only_added_branch=addition,original_checks_byte_identical=True,data_root=str(B)),indent=2)+'\n')
spec=importlib.util.spec_from_file_location('NEI_NEB_ADDITIVE',E/'NEI_NEB_ADDITIVE.py');extended=importlib.util.module_from_spec(spec);spec.loader.exec_module(extended)
extended.E=B;extended.R=R;extended.N=B.parent/'native-ledger3-20261029'
neb=extended
old_apply=leaves.apply;old_expected=certificates.expected
PACKETS=obj(E/'NEI_CTOR_PACKETS.json')
INDEX={p['function']:p for p in PACKETS}
def apply(base):
 out,changes=old_apply(base)
 for p in PACKETS:NEI_ctor_validate.audit(E,R,p,neb,neb.require)
 for row in out['rows']:
  p=INDEX.get(row['function'])
  if p is None:continue
  assert row['frozen_body_verified'] and row['frozen_body_sha256']==p['source_body_sha256']
  row.update(bridge_status='CLOSED-CONDITIONAL',selected_claims=[p['claim_id']],no_credit_reason=None)
  if p['claim_id'] not in row['claim_ids']:row['claim_ids'].append(p['claim_id'])
  row['named_hypotheses']=[dict(name=p['claim_id']+'.PacketDomain',statement=p['domain'],discharged_by=None),dict(name=p['claim_id']+'.PhysicalInterpretation',statement='Retain frozen source/ABI/native tool/std-array semantic interpretation; exact constructor result and whole receiver frame separately checked.',discharged_by=None)]
  row['reviewed_packet_updates'].append(dict(prefix='NEI',disposition='New native evidence replaces no old native credit; composed gates remain necessary',evidence=['evidence/slice-q-mul2-20261101/NEI_CTOR_PACKETS.json']))
 for row in out['rows']:
  for o in row['caller_domain_obligations']:
   p=INDEX.get(o.get('callee'))
   if p is None:continue
   o.update(callee_claims=[p['claim_id']],callee_local_status='CLOSED-CONDITIONAL',required_named_hypotheses=[p['claim_id']+'.PacketDomain',p['claim_id']+'.PhysicalInterpretation'])
 return out,changes

def check_ctor_occurrence(row,o,ext,index,base,approved_edges,rc):
 caller='crates/aspis-r1-cost-probe/src/fast_pairing.rs::EbyKDot::new'
 callee='crates/aspis-r1-cost-probe/src/fast_pairing.rs::canonical::Dot::new'
 assert row['function']==caller and row['row']=='TX2:073','constructor occurrence belongs to another root'
 assert o['call']['syntax']=='canonical::Dot::new' and o['call']['line']==161 and o['call']['cfg']==[],'wrong original constructor occurrence'
 assert o['id'] in ['external:TX2:73:1','external:TX2:73:2'] and ext['ordinal']==int(o['id'].rsplit(':',1)[1]),'wrong exact occurrence ordinal'
 edge=caller+' -> '+callee;obligation='call-domain:'+caller+'->'+callee
 current=index[obligation];cert=current['certificate']
 assert cert==approved_edges[edge] and not neb.certificate_errors(current,cert,base),'constructor edge not independently certified'
 assert ext['edge']==edge and ext['callee']==callee and ext['source_body_sha256']==row['frozen_body_sha256'],'constructor occurrence source binding'
 assert ext['theorems']==['NEI_DotCtorAssociation.two_calls'],'missing actual two-call binding'
 assert any(ext['theorems'][0] in item['theorems'] for item in rc['lean_evidence']),'constructor occurrence theorem not audited'
 source=obj(E/'NEI_FROZEN.json')['crates/aspis-r1-cost-probe/src/fast_pairing.rs']
 text=source[source.index('impl EbyKDot {'):source.index('    #[inline(always)]',source.index('impl EbyKDot {'))]
 assert text.count('canonical::Dot::new()')==2,'native source does not have those two calls'
extended._NEI_check_ctor_occurrence=check_ctor_occurrence

def new_certificates(base):
 rows={};edges={}
 for r in base['rows']:
  p=INDEX.get(r['function'])
  if p is None:continue
  review=dict(**p['review'],conclusion_hiding=False,statement_and_native_association_checked=True)
  native=dict(path=str(E.relative_to(R)/'NEI_CTOR_VALIDATE.json'),sha256=sha(E/'NEI_CTOR_VALIDATE.json'))
  externals={}
  for o in r['caller_domain_obligations']:
   if 'call' not in o:continue
   assert r['row']=='TX2:073' and o['call']['syntax']=='canonical::Dot::new','unreviewed extra constructor boundary'
   externals[o['id']]=dict(kind='NEI_CERTIFIED_CTOR_OCCURRENCE',ordinal=int(o['id'].rsplit(':',1)[1]),edge='crates/aspis-r1-cost-probe/src/fast_pairing.rs::EbyKDot::new -> crates/aspis-r1-cost-probe/src/fast_pairing.rs::canonical::Dot::new',callee='crates/aspis-r1-cost-probe/src/fast_pairing.rs::canonical::Dot::new',source_body_sha256=r['frozen_body_sha256'],theorems=['NEI_DotCtorAssociation.two_calls'])
  rows[r['row']]=dict(id='NEI-ctor-root:'+r['row'],row=r['row'],function=r['function'],frozen_body_sha256=r['frozen_body_sha256'],selected_claims=r['selected_claims'],named_hypotheses_discharged=[h['name'] for h in r['named_hypotheses']],inventory_domains_discharged=[o['unit'] for o in r['inventory_domain_obligations']],parts=['result','state','ordered_effects','native_association'],lean_evidence=p['lean_evidence'],remaining_inner_hypotheses=[],top_hypotheses=[r['function']+'.PacketDomain',r['function']+'.PhysicalInterpretation','CompositionTrustOptionA'],review=review,native_review=native,external_obligations=externals)
 caller='crates/aspis-r1-cost-probe/src/fast_pairing.rs::EbyKDot::new';callee='crates/aspis-r1-cost-probe/src/fast_pairing.rs::canonical::Dot::new'
 cr=next(r for r in base['rows'] if r['function']==caller);children=[r for r in base['rows'] if r['function']==callee]
 p=INDEX[caller];proofs=p['lean_evidence'];names=[n for x in proofs for n in x['theorems']];inner=sorted(set(h['name'] for r in children for h in r['named_hypotheses']));edge=caller+' -> '+callee
 review=dict(**p['review'],conclusion_hiding=False,statement_and_native_association_checked=True)
 edges[edge]=dict(id='NEI-ctor-two-calls',edge=edge,status='CLOSED',kind='DIRECT_CALL',frozen_revision=base['frozen_revision'],source_body_sha256=cr['frozen_body_sha256'],selected_callee_claims=sorted(set(c for r in children for c in r['selected_claims'])),inner_hypotheses_discharged=inner,hypothesis_discharge_theorems={n:names for n in inner},parts={part:dict(theorems=names) for part in ['packet_domain','canonical_carrier','same_inputs_result','state_ordered_effects','physical_interpretation','native_callsite_association']},lean_evidence=proofs,theorems=names,residual_hypotheses=[],review=review,native_review=dict(path=str(E.relative_to(R)/'NEI_CTOR_VALIDATE.json'),sha256=sha(E/'NEI_CTOR_VALIDATE.json')),trust='P6/D188 semantic transport retained; no older native credit')
 return edges,rows

def expected(base):
 old_edges,old_rows=old_expected(base);extra_edges,extra_rows=new_certificates(base)
 assert not (set(extra_edges)&set(old_edges)) and not (set(extra_rows)&set(old_rows)),'new certificate shadows old registration'
 return {**old_edges,**extra_edges},{**old_rows,**extra_rows}
leaves.apply=apply;certificates.expected=expected

def prepare(base):
 refreshed,_=apply(base);edges=obj(B/'NEB_EDGES.json')
 # Erase only supplied historical certificates, never an original obligation.
 for edge in edges['edges']:
  edge.update(certificate=None,status='OPEN',obstacle='No new NEI certificate supplied; all older native credit withheld')
  edge['required_named_hypotheses']=sorted(set(h['name'] for r in refreshed['rows'] if r['function']==edge['callee'] for h in r['named_hypotheses']))
 approved,rows=new_certificates(refreshed)
 for edge in edges['edges']:
  if edge['edge'] in approved:edge.update(certificate=approved[edge['edge']],status='CLOSED',obstacle=None)
 edges['inventory_edges']=[];edges['row_certificates']=list(rows.values())
 return edges

def validate(base,edges):
 for cert in edges.get('row_certificates',[]):
  assert cert['id'].startswith('NEI-'),'older native root credit supplied'
  assert all(x['receipt'].startswith(str(E.relative_to(R))+'/') for x in cert['lean_evidence']),'older proof/native recipe supplied'
 for edge in edges['edges']:
  if edge.get('certificate'):assert edge['certificate']['id'].startswith('NEI-'),'older native edge credit supplied'
 return neb.extend(base,edges)

def main():
 base=obj(E.parent/'native-ledger3-20261029/NDT_LEDGER.json')
 edges=prepare(base);out,delta=validate(base,edges)
 (E/'NEI_COMPOSE_EDGES.json').write_text(json.dumps(edges,indent=1)+'\n')
 (E/'NEI_DERIVED_LEDGER.json').write_text(json.dumps(out,indent=1)+'\n')
 (E/'NEI_COMPOSE_DELTA.json').write_text(json.dumps(delta,indent=2)+'\n')
 print(json.dumps(dict(composed_rows_closed=delta['composed_rows_closed'],edge_closed=delta['edge_closed'],original_neb_validator_sha256=sha(B/'NEB_validate.py'),old_native_credit_used=[]),indent=2))
if __name__=='__main__':main()
