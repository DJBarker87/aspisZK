from pathlib import Path
import hashlib,json,subprocess
E=Path(__file__).resolve().parent;R=E.parent.parent;sha=lambda b:hashlib.sha256(b).hexdigest();obj=lambda p:json.loads(p.read_text());PIN='fc13d787ca70882e636cb6a1a7fe8435d3c0d79617715deae2ecef06cc4a5992'
def expected(base):
 subprocess.run(['python3',str(E/'NEB_scalar_leaf_review.py'),'--check'],check=True,stdout=subprocess.DEVNULL)
 assert sha((E/'NEB_TableCalls.lean').read_bytes())==PIN
 p=E/'NEB_L062/receipt.json';d=obj(p);assert d['exit_status']==0 and d['source_hashes']['NEB_TableCalls.lean']==PIN
 names=['NEB_TableCalls.'+n for n in ['constructor','table_body','selected_table','constructor_frame','table_frame','getter_frame']];assert all(any(a.startswith("'"+n+"' ") and 'sorryAx' not in a for a in d['print_axioms']) for n in names)
 proof=dict(receipt=str(p.relative_to(R)),receipt_sha256=sha(p.read_bytes()),theorems=names)
 review=E/'NEB_SCALAR_ASSOCIATION.md';rev=dict(path=str(review.relative_to(R)),sha256=sha(review.read_bytes()),conclusion_hiding=False,statement_and_native_association_checked=True);native=E/'NEB_SCALAR_REVIEW.json';nr=dict(path=str(native.relative_to(R)),sha256=sha(native.read_bytes()));field='crates/aspis-core/src/field.rs::CM31::new';table='crates/aspis-r1-cost-probe/src/fast_domain.rs::table_value';getter='crates/aspis-core/src/r0/domain.rs::FibreIndex::get';edges={};rows={}
 for fn,frame in [(field,'constructor_frame'),(table,'table_frame'),(getter,'getter_frame')]:
  for r in base['rows']:
   if r['function']!=fn:continue
   assert r['bridge_status']=='CLOSED-CONDITIONAL' and r['selected_claims']
   ext={o['id']:dict(kind='TRANSPARENT_M31_CONSTRUCTOR',syntax=o['call'].get('expression',o['call'].get('syntax')),theorems=['NEB_TableCalls.constructor']) for o in r['caller_domain_obligations'] if 'call' in o};assert all(v['syntax']=='M31' for v in ext.values())
   rows[r['row']]=dict(id='NEB-scalar-root:'+r['row'],row=r['row'],function=fn,frozen_body_sha256=r['frozen_body_sha256'],selected_claims=r['selected_claims'],named_hypotheses_discharged=[h['name'] for h in r['named_hypotheses']],inventory_domains_discharged=[o['unit'] for o in r['inventory_domain_obligations']],parts=['result','state','ordered_effects','native_association'],lean_evidence=[proof],remaining_inner_hypotheses=[],top_hypotheses=[fn+'.PacketDomain',fn+'.PhysicalInterpretation','NativeContractSemanticTransport'],review=rev,native_review=nr,external_obligations=ext)
 source=next(r for r in base['rows'] if r['function']==table);children=[r for r in base['rows'] if r['function']==field];inner=sorted(set(h['name'] for r in children for h in r['named_hypotheses']));edge=table+' -> '+field
 edges[edge]=dict(id='NEB-table-constructor-edge',edge=edge,status='CLOSED',kind='DIRECT_CALL',frozen_revision=base['frozen_revision'],source_body_sha256=source['frozen_body_sha256'],selected_callee_claims=sorted(set(c for r in children for c in r['selected_claims'])),inner_hypotheses_discharged=inner,hypothesis_discharge_theorems={n:['NEB_TableCalls.constructor','NEB_TableCalls.table_body','NEB_TableCalls.selected_table'] for n in inner},parts={part:dict(theorems=names) for part in ['packet_domain','canonical_carrier','same_inputs_result','state_ordered_effects','physical_interpretation','native_callsite_association']},lean_evidence=[proof],theorems=names,residual_hypotheses=[],review=rev,native_review=nr,trust='NativeContractSemanticTransport: transparent executed context; reclassification, never removal')
 return edges,rows
