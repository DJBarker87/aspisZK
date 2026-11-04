"""Additive union: inherited checks unchanged; exact own recipes fail closed."""
from pathlib import Path
import json,lzma,hashlib,copy,sys
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parent.parent
from NEV_accum_packet import packet,proof
from NEV_prefix_validate import neb
from NEV_composition import context
obj=lambda p:json.loads(Path(p).read_text())
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
ACC='crates/aspis-r1-cost-probe/src/verifier.rs::accumulate_batched_with_node'
NEW={'TX1:185','TX2:111','TX1:188','TX2:113','TX1:190','TX2:117'}
REVIEW=E/'NEV_ACCUM_ASSOCIATION.md'
def inputs():
 # Original NEI+prefix gates replayed unchanged to validate their local rows.
 c,p,prepare,validate=context();base=obj(E.parent/'native-ledger3-20261029/NDT_LEDGER.json')
 ownEdges=prepare(base);own,delta=validate(base,ownEdges)
 assert own==obj(E/'NEV_PREFIX_DERIVED_LEDGER.json')
 assert ownEdges==obj(E/'NEV_PREFIX_EDGES.json')
 import NEV_materialize_net as material
 inherited=material.run()
 assert sum(x['composed_status']=='CLOSED' for x in inherited['rows'])==134
 netEdges=obj(material.C/'NET_EDGES.json')
 return own,ownEdges,inherited,netEdges,packet()
def recipes(own,ownEdges,inherited,netEdges,pack):
 out=copy.deepcopy(inherited);index={r['row']:r for r in out['rows']}
 for row in own['rows']:
  if row['row'] in NEW:
   assert row['composed_status']=='CLOSED' and index[row['row']]['composed_status']=='OPEN'
   assert row['frozen_body_sha256']==index[row['row']]['frozen_body_sha256']
   index[row['row']].clear();index[row['row']].update(copy.deepcopy(row))
 accRows=[r for r in out['rows'] if r['function']==ACC];assert {r['row'] for r in accRows}=={'TX1:182','TX2:108'}
 for row in accRows:
  assert row['composed_status']=='OPEN'
  row.update(bridge_status='CLOSED-CONDITIONAL',selected_claims=['NEV::accumulate'],no_credit_reason=None)
  row['claim_ids']+=['NEV::accumulate']
  row['named_hypotheses']=[dict(name='NEV::accumulate.'+kind,statement=pack['domain'],discharged_by=None) for kind in ['PacketDomain','PhysicalInterpretation']]
 review=dict(path=str(REVIEW.relative_to(R)),sha256=sha(REVIEW),conclusion_hiding=False,statement_and_native_association_checked=True)
 I=E.parent/'slice-q-mul2-20261101/NEI_L136/receipt.json'
 names=['NEI_ReleaseField.actual_'+n for n in ['m_mul','m_sub','m_double','qm_mul','wide_add']]
 compat=dict(receipt=str(I.relative_to(R)),receipt_sha256=sha(I),theorems=names)
 for name in names:neb.check_receipt(compat,name)
 freshFuncs={index[k]['function'] for k in NEW}|{ACC}
 edges=copy.deepcopy(netEdges);old={e['edge']:e for e in ownEdges['edges']};certs={};rowcerts={}
 # Every imported CLOSED edge remains byte-identical. Fresh recipes are only
 # for OPEN edges whose caller is one of our six imported rows or accumulation.
 for edge in edges['edges']:
  if edge['status']=='CLOSED' or edge['caller'] not in freshFuncs:continue
  if edge['caller']==ACC:
   target=edge['callee'];short=target.split('::')[-2:]
   selected=short in [['M31','mul'],['M31','sub'],['M31','double'],['QM31','mul'],['WideExact','add'],['WideExact','mul_qm31'],['WideExact','from_qm31']] or target.endswith(('::value','::BatchedWeights::push','::basis_at','::accumulated_weight_at'))
   edge.update(selected_target=selected,classification='PURE_TYPED_CALL' if selected else 'CONSERVATIVE_ALTERNATIVE',static_resolution='Actual NEI_E005 emitted receiver types; NEV_RowStep/TailModel/BasisOuterStep + same-body native cut logs; exact reviewed occurrence list')
   evidence=pack['lean_evidence']+[compat]
  else:
   source=old[edge['edge']];assert source['status']=='CLOSED'
   edge.update(**{k:source[k] for k in ['selected_target','classification','static_resolution']})
   evidence=source['certificate']['lean_evidence']+[compat]
  children=[r for r in out['rows'] if r['function']==edge['callee']]
  assert children and all(r['composed_status']=='CLOSED' for r in children)
  named=sorted({h['name'] for r in children for h in r['named_hypotheses']})
  audited=[n for p in evidence for n in p['theorems']]
  cert=dict(id='NEV-union:'+edge['obligation_id'],edge=edge['edge'],status='CLOSED',kind='DIRECT_CALL' if edge['selected_target'] is not False else 'STATIC_UNREACHABLE',frozen_revision=out['frozen_revision'],source_body_sha256=edge['source_body_sha256'],selected_callee_claims=sorted({x for r in children for x in r['selected_claims']}),inner_hypotheses_discharged=named,hypothesis_discharge_theorems={h:audited for h in named},parts={p:dict(theorems=audited) for p in ['packet_domain','canonical_carrier','same_inputs_result','state_ordered_effects','physical_interpretation','native_callsite_association']},lean_evidence=evidence,theorems=audited,residual_hypotheses=[],review=review)
  assert not neb.certificate_errors(edge,cert,out),neb.certificate_errors(edge,cert,out)
  edge.update(certificate=cert,status='CLOSED',obstacle=None,required_named_hypotheses=named);certs[edge['edge']]=copy.deepcopy(cert)
 lookup={e['obligation_id']:e for e in edges['edges']}
 for row in out['rows']:
  if row['row'] not in NEW|{'TX1:182','TX2:108'}:continue
  if row['function']==ACC:
   assert row['frozen_body_sha256']==next(e['source_body_sha256'] for e in edges['edges'] if e['caller']==ACC)
   external={o['id']:(o['call'].get('expression',o['call'].get('syntax')),o['call']['line']) for o in row['caller_domain_obligations'] if 'call' in o}
   assert set(external.values())==({('a.weights.len',278),('E::from_m31',285)} | ({('weights.value',283)} if row['row']=='TX2:108' else set()))
   if row['row']=='TX2:108':
    inactive=next(o for o in row['caller_domain_obligations'] if o.get('call',{}).get('syntax')=='weights.value');assert inactive['call']['resolution']=='disabled release cfg' and inactive['call']['cfg']==['#[cfg(feature="prover")]']
    for native in pack['native_pairs']:
     graph=obj(E/(native['positive']+'-graph-check.json')) if 'positive' in native else None
     if graph:assert all('prover' not in p['features'] for p in graph['resolved_features_all_crates'] if p['name']=='aspis-r1-cost-probe')
   rc=dict(id='NEV-accum-root:'+row['row'],function=ACC,domain=pack['domain'],lean_evidence=pack['lean_evidence'],parts=['result','state','ordered_effects','native_association'],external_obligations=external,remaining_inner_hypotheses=[],review=review,native_pairs=pack['native_pairs'],copy_controls=pack['copy_controls'])
   rowcerts[row['row']]=rc
   for h in row['named_hypotheses']:h['discharged_by']=rc['id']
   for o in row['inventory_domain_obligations']:o.update(status='CLOSED',discharged_by=rc['id'])
  for obligation in row['caller_domain_obligations']:
   if 'callee' in obligation:
    e=lookup[obligation['id']];assert e['status']=='CLOSED'
    obligation.update(status='CLOSED',discharged_by=e['certificate']['id'])
   else:
    if row['function']==ACC:obligation.update(status='CLOSED',discharged_by=rowcerts[row['row']]['id']+':external')
    else:assert obligation['status']=='CLOSED'
  assert all(o['status']=='CLOSED' for o in row['caller_domain_obligations']+row['inventory_domain_obligations'])
  assert all(h['discharged_by'] for h in row['named_hypotheses'])
  row.update(composed_status='CLOSED',open_transitive_dependencies=[])
 return out,edges,certs,rowcerts

def validate(out,edges,approved,rowcerts,inherited,netEdges):
 assert len(edges['edges'])==257 and {e['edge'] for e in edges['edges']}==set(obj(E.parent/'slice-q-compose-20261029/NEB_SCOPE.json')['slice']['internal_edges'])
 before={r['row']:r for r in inherited['rows']};baseEdges={e['edge']:e for e in netEdges['edges']}
 for r in out['rows']:
  if before[r['row']]['composed_status']=='CLOSED':assert r==before[r['row']],'inherited row changed'
 for edge in edges['edges']:
  assert edge['caller']+' -> '+edge['callee']==edge['edge']
  if baseEdges[edge['edge']]['status']=='CLOSED':assert edge==baseEdges[edge['edge']],'inherited edge changed'
  elif edge['status']=='CLOSED':
   assert edge['certificate']==approved[edge['edge']],'unregistered certificate'
   assert not neb.certificate_errors(edge,edge['certificate'],out)
 for key in ['trust_rows','quarantine','headline','frozen_revision']:assert out[key]==inherited[key]
 assert all(r['composed_status']=='OPEN' for r in out['rows'] if r['function'] in obj(E.parent/'slice-q-compose-20261029/NEB_SCOPE.json')['slice']['roots'])
 assert sum(r['composed_status']=='CLOSED' for r in out['rows'])==142
 assert set(rowcerts)=={'TX1:182','TX2:108'}
 p=packet()
 for key,rc in rowcerts.items():
  assert rc['function']==ACC and rc['domain']==p['domain']
  assert rc['lean_evidence']==p['lean_evidence'] and rc['native_pairs']==p['native_pairs'] and rc['copy_controls']==p['copy_controls']
  assert rc['parts']==['result','state','ordered_effects','native_association'] and rc['remaining_inner_hypotheses']==[]
  assert set(map(tuple,rc['external_obligations'].values()))==({('a.weights.len',278),('E::from_m31',285)} | ({('weights.value',283)} if key=='TX2:108' else set()))
  review=rc['review'];assert sha(R/review['path'])==review['sha256'] and review['conclusion_hiding'] is False and review['statement_and_native_association_checked'] is True
  row=next(r for r in out['rows'] if r['row']==key)
  assert row['selected_claims']==['NEV::accumulate'] and all(h['statement']==p['domain'] and h['discharged_by']==rc['id'] for h in row['named_hypotheses'])
  assert all(o['status']=='CLOSED' for o in row['caller_domain_obligations']+row['inventory_domain_obligations'])
 return True
if __name__=='__main__':
 own,oe,base,be,p=inputs();out,edges,certs,roots=recipes(own,oe,base,be,p);validate(out,edges,certs,roots,base,be)
 (E/'NEV_UNION_CERTIFICATES.json').write_text(json.dumps(dict(edges=certs,rows=roots),separators=(',',':'))+'\n')
 (E/'NEV_DERIVED_LEDGER.json').write_text(json.dumps(out,separators=(',',':'))+'\n')
 (E/'NEV_EDGES.json').write_text(json.dumps(edges,separators=(',',':'))+'\n')
 closed=[r['row'] for r in out['rows'] if r['composed_status']=='CLOSED'];new=['TX1:185','TX2:111','TX1:182','TX2:108']
 delta=dict(schema='NEV-union-v1',composed_rows_closed=closed,newly_closed=new,total=len(closed),edge_closed=sum(e['status']=='CLOSED' for e in edges['edges']),roots='OPEN',inherited_NET_closed=134,imported_NEI_new_six=sorted(NEW),trust='P6/D188 option A reclassification, never removal')
 for name in ['NEV_LEDGER_DELTA.json','NEV_CLOSED.json']:(E/name).write_text(json.dumps(delta,indent=2)+'\n')
 print(json.dumps({k:v for k,v in delta.items() if k not in ['composed_rows_closed']}))
