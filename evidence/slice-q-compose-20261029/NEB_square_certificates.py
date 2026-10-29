"""Exact arbitrary-scalar loop recipe; adopted native step plus Lean induction."""
from pathlib import Path
import hashlib,json,subprocess
E=Path(__file__).resolve().parent;R=E.parent.parent;sha=lambda b:hashlib.sha256(b).hexdigest();obj=lambda p:json.loads(p.read_text())
PIN='d28f229923e1e40fdd4b2e26165ec63e3d985c789d4888d123fce91652fb9c38'
def expected(base):
 subprocess.run(['python3',str(E/'NEB_square_review.py'),'--check'],check=True,stdout=subprocess.DEVNULL)
 assert sha((E/'NEB_SquareComposition.lean').read_bytes())==PIN
 p=E/'NEB_L069/receipt.json';d=obj(p);assert d['exit_status']==0 and d['source_hashes']=={'NEB_SquareComposition.lean':PIN}
 names=['NEB_SquareComposition.'+n for n in ['cell','loop_frame','trace_frame']]
 assert all(any(a.startswith("'"+n+"' ") and 'sorryAx' not in a for a in d['print_axioms']) for n in names)
 ps=[dict(receipt=str(p.relative_to(R)),receipt_sha256=sha(p.read_bytes()),theorems=names)]
 fn='crates/aspis-core/src/field.rs::square_n';source=next(r for r in base['rows'] if r['function']==fn);review=E/'NEB_SQUARE_ASSOCIATION.md';rev=dict(path=str(review.relative_to(R)),sha256=sha(review.read_bytes()),conclusion_hiding=False,statement_and_native_association_checked=True);native=E/'NEB_SQUARE_REVIEW.json';nr=dict(path=str(native.relative_to(R)),sha256=sha(native.read_bytes()));edges={};rows={}
 for e in obj(E/'NEB_EDGES.json')['edges']:
  if e['caller']!=fn:continue
  assert e['selected_target']==e['callee'].endswith('::M31::mul')
  children=[r for r in base['rows'] if r['function']==e['callee']];inner=sorted(set(h['name'] for r in children for h in r['named_hypotheses']));claims=sorted(set(c for r in children for c in r['selected_claims']))
  edges[e['edge']]=dict(id='NEB-square-edge:'+e['obligation_id'],edge=e['edge'],status='CLOSED',kind='DIRECT_CALL' if e['selected_target'] else 'STATIC_UNREACHABLE',frozen_revision=base['frozen_revision'],source_body_sha256=source['frozen_body_sha256'],selected_callee_claims=claims,inner_hypotheses_discharged=inner,hypothesis_discharge_theorems={n:names for n in inner},parts={part:dict(theorems=names) for part in ['packet_domain','canonical_carrier','same_inputs_result','state_ordered_effects','physical_interpretation','native_callsite_association']},lean_evidence=ps,theorems=names,residual_hypotheses=[],review=rev,native_review=nr,trust='NativeContractSemanticTransport: adopted arbitrary scalar step and existing trace induction; reclassification, never removal')
 for r in base['rows']:
  if r['function']!=fn:continue
  assert not any('call' in o for o in r['caller_domain_obligations'])
  rows[r['row']]=dict(id='NEB-square-root:'+r['row'],row=r['row'],function=fn,frozen_body_sha256=r['frozen_body_sha256'],selected_claims=r['selected_claims'],named_hypotheses_discharged=[h['name'] for h in r['named_hypotheses']],inventory_domains_discharged=[o['unit'] for o in r['inventory_domain_obligations']],parts=['result','state','ordered_effects','native_association'],lean_evidence=ps,remaining_inner_hypotheses=[],top_hypotheses=[fn+'.PacketDomain',fn+'.PhysicalInterpretation','NativeContractSemanticTransport'],review=rev,native_review=nr,external_obligations={})
 return edges,rows
