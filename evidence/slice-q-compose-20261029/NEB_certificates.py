#!/usr/bin/env python3
"""Concrete reviewed certificate recipes; no arbitrary theorem-name promotion."""
from pathlib import Path
import hashlib,json,subprocess
E=Path(__file__).resolve().parent;R=E.parent.parent
sha=lambda b:hashlib.sha256(b).hexdigest()
APPROVED_REDUCER_LEAN_SHA='9a32e600871c4128893e1702ce5d8d4eedcd78566fd376626900534889019d78'
def obj(p):return json.loads(p.read_text())
def expected(baseline):
 # A recipe becomes available only after its exact native and Lean targets pass.
 native=E/'NEB_NATIVE_REVIEW.json'
 source=E/'NEB_ReducerCall.lean'
 candidates=[]
 for p in E.glob('NEB_L*/receipt.json'):
  d=obj(p)
  if d.get('module')=='NEB_ReducerCall' and d['exit_status']==0 and d['source_hashes'].get('NEB_ReducerCall.lean')==sha(source.read_bytes()):candidates.append((p,d))
 if not native.exists() or not candidates:return {},{}
 assert sha(source.read_bytes())==APPROVED_REDUCER_LEAN_SHA,'unreviewed reducer statement/source change'
 subprocess.run(['python3',str(E/'NEB_native_review.py'),'--check'],cwd=R,check=True,stdout=subprocess.DEVNULL)
 nr=obj(native);assert len(nr['native_results'])==8
 p,d=sorted(candidates,key=lambda v:v[0].as_posix())[-1]
 for theorem in ['all_domain','reference','wrapper','value','state_effects']:
  assert any(a.startswith("'NEB_ReducerCall."+theorem+"' ") and 'sorryAx' not in a for a in d['print_axioms'])
 ex=obj(E/'NEB_EXTRACTION_PINS.json');assert ex['exit']==0
 assert ex['charon_sha256']=='daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8'
 assert ex['aeneas_sha256']=='c0cf4fccb0879db4ce342da991f6215732a19fc01345b9eec84e632f4673b958'
 assert ex['rust_reference_sha256']==sha((E/'NEB_reference.rs').read_bytes())
 # Extraction output and actual compiled reference must be the same bytes.
 for n in ['Types','Funs']:
  key='NEB_extracted/NEB_Reference/'+n+'.lean';raw=(E/'NEB_Reference'/(n+'.lean')).read_bytes()
  assert sha(raw)==ex['outputs'][key]
 review=E/'NEB_REDUCER_ASSOCIATION.md'
 proof=dict(receipt=str(p.relative_to(R)),receipt_sha256=sha(p.read_bytes()),theorems=['NEB_ReducerCall.'+t for t in ['all_domain','reference','wrapper','value','state_effects']])
 rev=dict(path=str(review.relative_to(R)),sha256=sha(review.read_bytes()),conclusion_hiding=False,statement_and_native_association_checked=True)
 field='crates/aspis-core/src/field.rs::';caller=field+'M31::reduce_u64';callee=field+'reduce_u64'
 source_rows=[r for r in baseline['rows'] if r['function']==caller]
 names=sorted(set(h['name'] for r in baseline['rows'] if r['function']==callee for h in r['named_hypotheses']))
 callee_claims=sorted(set(c for r in baseline['rows'] if r['function']==callee for c in r['selected_claims']))
 def part(*names):return dict(theorems=['NEB_ReducerCall.'+n for n in names])
 edge=caller+' -> '+callee
 cert=dict(id='NEB-reducer-call',edge=edge,status='CLOSED',kind='DIRECT_CALL',frozen_revision=baseline['frozen_revision'],source_body_sha256=source_rows[0]['frozen_body_sha256'],selected_callee_claims=callee_claims,inner_hypotheses_discharged=names,hypothesis_discharge_theorems={n:['NEB_ReducerCall.all_domain'] if n.endswith('PacketDomain') else ['NEB_ReducerCall.reference','NEB_ReducerCall.wrapper','NEB_ReducerCall.state_effects'] for n in names},parts=dict(packet_domain=part('all_domain'),canonical_carrier=part('value'),same_inputs_result=part('reference','wrapper'),state_ordered_effects=part('state_effects'),physical_interpretation=part('reference','wrapper'),native_callsite_association=part('wrapper')),lean_evidence=[proof],theorems=proof['theorems'],residual_hypotheses=[],review=rev,native_review=dict(path=str(native.relative_to(R)),sha256=sha(native.read_bytes())),trust='NativeContractSemanticTransport: reclassification, never removal')
 rows={}
 for row in baseline['rows']:
  if row['function'] not in [caller,callee]:continue
  names=[h['name'] for h in row['named_hypotheses']]
  external={o['id']:dict(kind='TRANSPARENT_M31_CONSTRUCTOR',syntax=o['call'].get('expression',o['call'].get('syntax')),theorems=['NEB_ReducerCall.wrapper','NEB_ReducerCall.state_effects']) for o in row['caller_domain_obligations'] if 'call' in o}
  assert all(v['syntax']=='M31' for v in external.values())
  rows[row['row']]=dict(id='NEB-reducer-root:'+row['row'],row=row['row'],function=row['function'],frozen_body_sha256=row['frozen_body_sha256'],selected_claims=row['selected_claims'],named_hypotheses_discharged=names,inventory_domains_discharged=[o['unit'] for o in row['inventory_domain_obligations']],parts=['result','state','ordered_effects','native_association'],lean_evidence=[proof],remaining_inner_hypotheses=[],top_hypotheses=[row['function']+'.PacketDomain',row['function']+'.PhysicalInterpretation','NativeContractSemanticTransport'],review=rev,native_review=cert['native_review'],external_obligations=external)
 from NEB_additive_certificates import expected as additive
 extra_edges,extra_rows,_=additive(baseline)
 from NEB_representation_certificates import expected as representation
 representation_edges,representation_rows=representation(baseline)
 from NEB_field_certificates import expected as field_expected
 field_edges,field_rows,_=field_expected(baseline)
 from NEB_scalar_certificates import expected as scalar_expected
 scalar_edges,scalar_rows=scalar_expected(baseline)
 from NEB_leaf_certificates import expected as leaf_expected
 leaf_edges,leaf_rows=leaf_expected(baseline)
 from NEB_square_certificates import expected as square_expected
 square_edges,square_rows=square_expected(baseline)
 return {edge:cert,**square_edges,**extra_edges,**representation_edges,**field_edges,**scalar_edges,**leaf_edges},{**rows,**square_rows,**extra_rows,**representation_rows,**field_rows,**scalar_rows,**leaf_rows}
if __name__=='__main__':
 from NEB_leaf_updates import apply,resolutions
 base,_=apply(obj(E.parent/'native-ledger3-20261029/NDT_LEDGER.json'));edges=obj(E/'NEB_EDGES.json')
 edges['edges']=[resolutions(e) for e in edges['edges']]
 for e in edges['edges']:
  e['required_named_hypotheses']=sorted(set(h['name'] for r in base['rows'] if r['function']==e['callee'] for h in r['named_hypotheses']))
 expected_edges,rows=expected(base)
 for edge in edges['edges']:
  if edge['edge'] in expected_edges:edge.update(certificate=expected_edges[edge['edge']],status='CLOSED',obstacle=None)
 from NEB_additive_certificates import expected as additive
 _,_,extra=additive(base)
 from NEB_field_certificates import expected as field_expected
 _,_,field_extra=field_expected(base)
 edges['inventory_edges']=extra+field_extra
 edges['row_certificates']=list(rows.values())
 (E/'NEB_EDGES.json').write_text(json.dumps(edges,indent=1)+'\n')
 print(json.dumps(dict(edge_certificates=len(expected_edges),root_certificates=len(rows))))
