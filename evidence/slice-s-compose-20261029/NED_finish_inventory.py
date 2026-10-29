"""Record every remaining member and exact edge obligation without promotion."""
from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent
read=lambda p:json.loads(p.read_text())
assert len(list(E.glob('NED_L*/receipt.json')))==150 and len(list(E.glob('NED_K*/receipt.json')))==40
scope=read(E/'NED_SCOPE.json');edges=read(E/'NED_EDGES.json')['edges'];roots=scope['slice']['roots']
why={
'decode_public_statement_box':'Native borrowed account window, Box result/error forwarding and ordered effects are not fully associated; imported common/afterstate packets leave their child instances explicit.',
'validate_pool_v1_pair_forest_terminal_statement_v1':'K034/K035 prove frozen caller control with arbitrary child replies. Each cached reply still needs the selected callee bridge on the identical carrier and state; inner PhysicalInterpretation names remain. Model equality is not that native instantiation.',
'encode_pool_v1_pair_forest_terminal_statement_v1':'Native call windows are established. Complete 1880-byte returned array, child Results, local update/frame and ordered effects remain; model loop and total lower encoding laws do not establish native copy assembly.',
'reconstruct_asq8_statement':'Cross-family carrier maps are total, but the actual native reconstruction/decoder/validator composition and its error/state/effect association remain uninstantiated.',
'decode_pool_v1_pair_forest_terminal_request_v1':'K036/K037 establish same 216-byte payment payload/tag. Returned Box/public value, common/lane decoding, error propagation and ordered effects still require native child associations.',
'scan_proof_buffer':'A cohort loop-congruence theorem exists; a native arbitrary-prestate iteration tied to the same account observations and ordered effects is missing. Whole-buffer unwinding is forbidden.',
'emit_result':'Complete native result encoding, destination-account mutations, runtime reply/error and ordered effects need association. A pure result codec or scalar selector is insufficient.'}
rows=[]
for m in scope['members']:
 f=m['function'];es=[e for e in edges if e['caller']==f]
 hs=[h['name'] for h in m['named_hypotheses']]
 rows.append(dict(function=f,status='OPEN',baseline_bridge_status=m['bridge_status'],inner_names_retained=hs,
  internal_edges=[dict(edge=e['edge'],classification=e['classification'],obstacle=e['obstacle']) for e in es],
  exact_selected_claims=[dict(id=c.get('claim_id'),domain=c.get('source_claim_text'),feature_parity=c.get('feature_parity'),limitations=c.get('limitations')) for c in m['selected_claims']],
  reason_no_composed_credit=why.get(f.split('::')[-1], 'The selected packet remains conditional on the listed exact domain/physical names. No accepted same-call native result/state/effect certificate discharges these names and the listed conservative edges.'),
  further_native_work='Needs an actual caller native association or a pre-existing accepted packet instantiated on the same values; no additional raw Kani pass is inferred from pure Lean transport.',
  further_lean_work='Call-domain/carrier and effect-frame composition must be proved for every listed actual site. These may continue in Lean after the native instance is supplied; Kani exhaustion alone is not their discharge.'))
(E/'NED_REMAINING.json').write_text(json.dumps(dict(slice='S',composed_roots_closed=0,root_obstacles={r:why[r.split('::')[-1]] for r in roots},members=rows,budget_stop='40 Kani and 150 actual Lean scopes consumed; no further proof launch authorized'),indent=1)+'\n')
print('Recorded',len(rows),'members and',len(edges),'internal edges; no promotion')
