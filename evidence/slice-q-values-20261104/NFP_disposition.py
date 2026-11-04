"""Additive support disposition. No unproved native/model join is registered."""
from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent
obj=lambda p:json.loads(p.read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
QUERY='crates/aspis-r1-cost-probe/src/candidate.rs::query_values'
LOOP='crates/aspis-r1-cost-probe/src/candidate.rs::query_loop'
ROWS={'TX1:089':QUERY,'TX2:059':QUERY,'TX1:088':LOOP,'TX2:058':LOOP}
TRUST='P6/D188 option-A native semantic transport reclassified, never removed; L154 statement parameter; RuntimePersistence, RuntimeReturnData and RuntimeMemcmp accepted; SDK/std/copy/allocator/ABI/runtime/physical/source-to-ELF and security premises retained'
def expected():
 p=E.parent/'slice-q-mul9-20261104';base=obj(p/'NFM_EDGES.json')
 def ref(n):return dict(path=str((p/n).relative_to(E.parent.parent)),sha256=sha(p/n))
 selected=[]
 for edge in obj(E/'NFP_EDGE_INTAKE.json'):
  callee=edge['callee'];s=dict(edge=edge['edge'],status=edge['status'],certificate=edge['certificate'],source_body_sha256=edge['source_body_sha256'])
  if edge['status']=='OPEN':
   s.update(NFP_status='OPEN: local support only',superseded_obstacle='Observer=None is admitted by (ae); the previous blanket Option<fn> reason is superseded for this route',remaining='Final SAME-execution call-domain/state/ordered-effect installation into the caller packet is not proved. No complete caller packet is registered.')
   if callee.endswith('accumulate_batched_with_node'):s['remaining']='The standalone NEV accumulated-row packet cannot jointly import with the selected Phase owner (L038); coherent retarget and complete caller installation required.'
   if callee==QUERY:s['remaining']='Callee query_values remains OPEN. Native one-step windows and NFG finite partial-Result induction do not discharge an open child.'
  selected.append(s)
 edges=dict(schema='NFP-additive-edge-support-v1',slice='Q',baseline=ref('NFM_EDGES.json'),inventory_edge_count=len(base['edges']),inherited_closed=sum(r['status']=='CLOSED' for r in base['edges']),overrides=[],newly_closed=[],selected_edges=selected,qualification='Original 257-edge inventory retained by hash. Support is not a composed edge certificate.')
 closed=dict(schema='NFP-NDT-composed-v1',headline='AspisR1.RPx_Deployed.deployed',baseline=ref('NFM_CLOSED.json'),newly_closed=[],new_count=0,rows={k:dict(function=v,status='OPEN',reason='NFP_COHERENCE_FINDING.md plus NFP_REMAINING.md') for k,v in ROWS.items()},certificates=[],root_status='OPEN',cached_development_cohort=True,cold_release_replay=False,security_target_established=False,route_label_for_any_future_closure='CLOSED under (ae)',trust=TRUST)
 delta=dict(schema='NFP-additive-NFM-v1',baseline_validator=ref('NFM_validate.py'),headline=closed['headline'],newly_closed=[],new_count=0,newly_certified_edges=[],new_edge_count=0,edge_total=edges['inventory_edge_count'],edge_closed=edges['inherited_closed'],query_values_incoming_edge_closed=False,rows={k:'OPEN' for k in ROWS},route='CLOSED under (ae)',route_rows=[],budget=dict(kani_used=76,kani_limit=100,lean_audit_used=60,lean_audit_limit=60,extraction_used=0,extraction_limit=3),security_target_established=False,sibling_combined_credit=False,trust=TRUST)
 return closed,edges,delta
if __name__=='__main__':
 for name,x in zip(['CLOSED','EDGES','LEDGER_DELTA'],expected()):(E/f'NFP_{name}.json').write_text(json.dumps(x,indent=2)+'\n')
