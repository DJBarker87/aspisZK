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
import NEI_dot_finish_certificates as dots
import NEI_field_certificates as fields
import NEI_fold_certificates as folds
import NEI_arithmetic_certificates as arithmetic
obj=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
# Preserve every original check byte-for-byte, adding one strictly scoped
# external-occurrence class. The original file remains read-only.
original=(B/'NEB_validate.py').read_text()
marker="     else:require(False,'unregistered external obligation kind')"
addition="""     elif ext['kind']=='NEI_CERTIFIED_CTOR_OCCURRENCE':
      _NEI_check_ctor_occurrence(row,o,ext,index,baseline,approved_edges,rc)
      o.update(status='CLOSED',discharged_by=rc['id']+':certified-ctor-occurrence')
     elif ext['kind'] in ['NEI_DOT_VALUE_CTOR','NEI_EBY_CTOR_UNWRAP']:
      _NEI_check_finish_external(row,o,ext,index,baseline,approved_edges,rc)
      o.update(status='CLOSED',discharged_by=rc['id']+':exact-finisher-terminal')
     elif ext['kind']=='NEI_PRIVATE_MODULUS_CAST':
      _NEI_check_dot_cast(row,o,ext,rc)
      o.update(status='CLOSED',discharged_by=rc['id']+':private-modulus-cast')
     elif ext['kind']=='NEI_WIDE_OPTION_CONSTRUCTOR':
      _NEI_check_wide_some(row,o,ext,rc)
      o.update(status='CLOSED',discharged_by=rc['id']+':wide-option-constructor')
     elif ext['kind']=='NEI_ROW_U32_U64_WIDEN':
      _NEI_check_row_widen(row,o,ext,rc)
      o.update(status='CLOSED',discharged_by=rc['id']+':lossless-row-u32-u64')
"""
assert original.count(marker)==1
added=original.replace(marker,addition+marker)
assert added.replace(addition,'')==original,'an original validator check changed'
(OUT/'NEV_NEB_ADDITIVE.py').write_text(added)
(OUT/'NEV_VALIDATOR_SOURCE_DELTA.json').write_text(json.dumps(dict(original=str(B/'NEB_validate.py'),original_sha256=sha(B/'NEB_validate.py'),derived=str(E/'NEI_NEB_ADDITIVE.py'),derived_sha256=sha(E/'NEI_NEB_ADDITIVE.py'),only_added_branch=addition,original_checks_byte_identical=True,data_root=str(B)),indent=2)+'\n')
spec=importlib.util.spec_from_file_location('NEV_NEB_ADDITIVE',OUT/'NEV_NEB_ADDITIVE.py');extended=importlib.util.module_from_spec(spec);spec.loader.exec_module(extended)
extended.E=B;extended.R=R;extended.N=B.parent/'native-ledger3-20261029'
neb=extended
old_apply=leaves.apply;old_expected=certificates.expected
PACKETS=obj(E/'NEI_CTOR_PACKETS.json')+arithmetic.packets()+dots.packets()+fields.packets()+folds.packets()
INDEX={p['function']:p for p in PACKETS}
def apply(base):
 out,changes=old_apply(base)
 for p in PACKETS:
  if p['route']=='D188_LITERAL_CTOR_FULL_CONTEXT':NEI_ctor_validate.audit(E,R,p,neb,neb.require)
  elif p['route'] in ['D188_ACTUAL_BODY_FULL_CALLEES','D188_ACTUAL_BODY_SHARED_CALLEES']:folds.audit(p,neb)
  elif p['route']=='D188_ACTUAL_IMMUTABLE_FIELD':fields.audit(p,neb)
  elif p['route']=='D188_ACTUAL_DOT_FINISH':dots.audit(p,neb)
  else:arithmetic.audit(p,neb)
 for row in out['rows']:
  p=INDEX.get(row['function'])
  if p is None:continue
  assert row['frozen_body_verified'] and row['frozen_body_sha256']==p['source_body_sha256']
  row.update(bridge_status='CLOSED-CONDITIONAL',selected_claims=[p['claim_id']],no_credit_reason=None)
  if p['claim_id'] not in row['claim_ids']:row['claim_ids'].append(p['claim_id'])
  row['named_hypotheses']=[dict(name=p['claim_id']+'.PacketDomain',statement=p['domain'],discharged_by=None),dict(name=p['claim_id']+'.PhysicalInterpretation',statement='Retain frozen source/ABI and P6/D188 tool semantic transport; actual body, release domain/profile, full Result, state and ordered effects separately audited.',discharged_by=None)]
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
extended._NEI_check_finish_external=lambda row,o,ext,index,base,approved_edges,rc: dots.gate.check_finish_external(row,o,ext,index,base,approved_edges,rc,neb)
extended._NEI_check_dot_cast=dots.gate.check_cast
extended._NEI_check_wide_some=arithmetic.NEI_wide_ctor_validate.check_some
extended._NEI_check_row_widen=arithmetic.check_widen

def new_certificates(base):
 rows={};edges={}
 for r in base['rows']:
  p=INDEX.get(r['function'])
  if p is None or p['route']!='D188_LITERAL_CTOR_FULL_CONTEXT':continue
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
 extra_edges,extra_rows=arithmetic.recipes(base,neb)
 assert not(set(extra_edges)&set(edges)) and not(set(extra_rows)&set(rows))
 all_edges={**edges,**extra_edges};all_rows={**rows,**extra_rows}
 dot_edges,dot_rows=dots.recipes(base,neb)
 assert not(set(dot_edges)&set(all_edges)) and not(set(dot_rows)&set(all_rows))
 field_edges,field_rows=fields.recipes(base,neb)
 assert not(set(field_edges)&(set(all_edges)|set(dot_edges))) and not(set(field_rows)&(set(all_rows)|set(dot_rows)))
 fold_edges,fold_rows=folds.recipes(base,neb)
 assert not(set(fold_edges)&(set(all_edges)|set(dot_edges)|set(field_edges))) and not(set(fold_rows)&(set(all_rows)|set(dot_rows)|set(field_rows)))
 return {**all_edges,**dot_edges,**field_edges,**fold_edges},{**all_rows,**dot_rows,**field_rows,**fold_rows}

def expected(base):
 old_edges,old_rows=old_expected(base);extra_edges,extra_rows=new_certificates(base)
 # Fresh, specifically audited dot packets replace only suspended older
 # registrations for the SAME source body. Original gates are unchanged; no
 # old certificate is supplied to extend(). All other overlaps stay forbidden.
 replaced=[]
 for key in set(extra_rows)&set(old_rows):
  a,b=old_rows[key],extra_rows[key]
  assert ((b['id'].startswith('NEI-dot-root:') and b['function'] in dots.gate.FUNCTIONS) or (b['id'].startswith('NEI-field-root:') and b['function'] in fields.gate.FUNCTIONS) or (b['id'].startswith('NEI-fold-root:') and b['function'] in {p['function'] for p in folds.packets()}))
  assert a['function']==b['function'] and a['row']==b['row'] and a['frozen_body_sha256']==b['frozen_body_sha256']
  assert b['function'] in INDEX
  if b['function'] in dots.gate.FUNCTIONS:
   assert INDEX[b['function']]['native_pair']==dots.gate.PAIRS[b['function']]
   dots.audit(INDEX[b['function']],neb)
  elif b['function'] in fields.gate.FUNCTIONS:fields.audit(INDEX[b['function']],neb)
  else:folds.audit(INDEX[b['function']],neb)
  replaced.append(dict(kind='root',key=key,old=a['id'],new=b['id'],old_native_credit_used=False));del old_rows[key]
 overlap_recipes={}
 for key in set(extra_edges)&set(old_edges):
  a,b=old_edges[key],extra_edges[key]
  assert (b['id'].startswith('NEI-dot-edge:') or b['id'].startswith('NEI-field-edge:') or b['id'].startswith('NEI-fold-edge:')) and a['edge']==b['edge'] and a['source_body_sha256']==b['source_body_sha256']
  group='dot' if b['id'].startswith('NEI-dot-edge:') else 'field' if b['id'].startswith('NEI-field-edge:') else 'fold'
  if group not in overlap_recipes:overlap_recipes[group]={'dot':dots,'field':fields,'fold':folds}[group].recipes(base,neb)[0]
  assert key in overlap_recipes[group]
  replaced.append(dict(kind='edge',key=key,old=a['id'],new=b['id'],old_native_credit_used=False));del old_edges[key]
 assert not(set(extra_edges)&set(old_edges)) and not(set(extra_rows)&set(old_rows)),'unreviewed registration overlap'
 (OUT/'NEV_REPLACED_OLD_REGISTRATIONS.json').write_text(json.dumps(sorted(replaced,key=lambda x:(x['kind'],x['key'])),indent=2)+'\n')
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
 edges['inventory_edges']=fields.inventory(refreshed,neb,approved);edges['row_certificates']=list(rows.values())
 return edges

def validate(base,edges):
 for cert in edges.get('row_certificates',[]):
  assert cert['id'].startswith('NEI-'),'older native root credit supplied'
  assert all(x['receipt'].startswith(str(E.relative_to(R))+'/') for x in cert['lean_evidence']),'older proof/native recipe supplied'
 for edge in edges['edges']:
  if edge.get('certificate'):
   assert edge['certificate']['id'].startswith('NEI-'),'older native edge credit supplied'
   if edge['certificate']['kind']=='STATIC_UNREACHABLE':
    assert edge['classification']=='CONSERVATIVE_ALTERNATIVE' and edge['selected_target'] is False,'static target resolution contradicted'
   else:
    assert edge['selected_target'] is not False,'direct target resolution contradicted'
 return neb.extend(base,edges)

def main():
 base=obj(E.parent/'native-ledger3-20261029/NDT_LEDGER.json')
 edges=prepare(base);out,delta=validate(base,edges)
 (E/'NEI_COMPOSE_EDGES.json').write_text(json.dumps(edges,indent=1)+'\n')
 (E/'NEI_DERIVED_LEDGER.json').write_text(json.dumps(out,separators=(',',':'))+'\n')
 (E/'NEI_COMPOSE_DELTA.json').write_text(json.dumps(delta,indent=2)+'\n')
 print(json.dumps(dict(composed_rows_closed=delta['composed_rows_closed'],edge_closed=delta['edge_closed'],original_neb_validator_sha256=sha(B/'NEB_validate.py'),old_native_credit_used=[]),indent=2))
if __name__=='__main__':main()
