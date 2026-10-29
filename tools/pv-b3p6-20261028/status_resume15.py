"""Report model results separately from actual source/dependency closure."""
from pathlib import Path
import json,hashlib,subprocess
D=Path('evidence/pv-b3p6-20261028');O=D/'resume15';old=json.loads((D/'resume14/link-status.json').read_text());receipts=json.loads((O/'receipt-index.json').read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
latest={}
for r in sorted(receipts,key=lambda r:r['attempt']):latest[r['module']]=r
accepted={m:r for m,r in latest.items()if r['exit']==0 and (D/'lean'/(m+'.lean')).is_file()and sha(D/'lean'/(m+'.lean'))==r['source_sha256']}
new={
'absorption_lanes_literal':('PV_B3P_AbsorptionSource15227','absorption_source_binding15'),
'occupancy_lanes_literal':('PV_B3P_NativeOccupancy15227','native_occupancy_binding15'),
'interpolate_three_constant_columns':('PV_B3P_InterpolationSource15227','interpolation_source_binding15'),
'poseidon_selectors':('PV_B3P_PoseidonSelectorCaller15227','native_poseidon_selectors_binding15'),
'add_schedule_lanes':('PV_B3P_ScheduleCaller15227','native_schedule_binding15')}
remaining={
'absorption_lanes_literal':'Macro source shape and bounded-read order have model laws; actual callee/index source association remains open.',
'add_digest_binding':'Native indexed stores, inline tweak/source helper correspondence and callee associations remain open.',
'add_path_lanes':'Actual sum/path/preweighted caller association remains open.',
'add_preweighted':'Bounded inclusive caller law and all eight call bounds compile; actual iterator, macro/index and packed-store association remain open.',
'add_schedule_lanes':'The ordered caller model uses both preweighted calls; actual semantic and mutable caller association remains open.',
'add_value_lanes':'Source-model instance retained; actual 33-slot iterator/mutable-store caller association awaits peer-owned D188/std obligations.',
'composition_parts':'Actual guards, selected claims, selector allocation, copy/Poseidon/semantic calls and both Horner loops remain unbound as one deployed source body.',
'equality_value':'Shared read/loan model and complete Result laws compile; source reference/index/primitive association remains open.',
'occupancy_lanes_literal':'All eight cells and range composition compile; actual source index/store and field-callee association remains open.',
'path_lanes_literal':'Source grammar, step and draft caching/fold proofs retained; whole source model is not compiled/credited.',
'poseidon_selectors':'Singleton range caller model compiles; actual shared source/sum caller association remains open.',
'public_digest_lanes':'Source range/partial-output model compiles; actual frontier, carry, field/index and digest-store source association remains open.',
'reconstruct_10':'Shared read/loan model and reverse complete Result laws compile; source reference/index/primitive association remains open.',
'semantic_initial_and_absorption':'Actual prepared selectors, initialization macro, two corrections and absorption composition remain open.',
'semantic_packed':'Actual ordered mutating caller, variant scalar terms and final insertions remain open.',
'sum_high':'Shared ordered ranges model compiles; actual outer slice and inner Range source associations remain open.',
'validate_transition':'Actual short-circuit checked-add/continue/frontier comparison source association remains open.',
'active_literal':'Source while model retained; actual frozen-mask call domain, index, field and mask-helper association remains open.',
'pattern_values_literal':'Source power and pattern while models compile; actual copy/index/field caller association remains open.',
'selector_mask_sum_16':'Guarded native-shaped model and read/subtraction safety compile; actual bit intrinsic/caller association remains open. Corrected zero behavior retained.',
'qm31_m31_dot':'Seven-element assertion/branch and two-chunk bounds compile; complete wrapping-channel source body and caller association remain open.',
'qm31_sum_products3_prepared':'Prior payload/array model retained; actual source matrix/caller association is peer-owned and not claimed here.',
'at_point':'Corrected layout=57/caller/native obligations retained; actual constructor/expand/sum association remains open.',
'evaluate_state_only_poseidon_oracle_projected':'Source caller model with native-shaped leading range compiles; actual slices, prepared payload and caller associations remain open.',
'expand':'Source slice, child-index and reverse frame bounds compile; actual coordinate/reverse iteration and stores remain open.',
'external_linear_lazy':'Complete local, column-sum and output source association remains open.',
'external_linear_packed':'Complete group, sum and output-map source association remains open.',
'external_local_packed_raw':'Complete source arithmetic, match bounds and release debug-assert association remains open.',
'full_round':'Source range model compiles; actual range/index/store and external-layer associations remain open.',
'full_round_m31_constants':'Source range model keeps both stores; actual mutable source/callee associations remain open.',
'full_round_m31_constants_packed':'Source range model keeps both stores; actual mutable source/callee associations remain open.',
'full_round_packed':'Source range model compiles; actual range/index/store and packed external-layer associations remain open.',
'internal_linear_lazy':'Both source loop phases and ordered model composition compile; actual source/helper/index/store association remains open.',
'interpolate_three_constant_columns':'Repeated source reads and sixteen-cell model composition compile; actual source primitive/callee association remains open.',
'interpolated_internal_pair':'Actual seven-row maps, dot calls and two-round source association remain open.',
'leading_pair_packed':'Source range model compiles; actual immutable copy, indexed writes, external layer and two native round associations remain open.'}
rows=[]
for r in old:
 n=r['function'];before=bool(r.get('model_instance') or r.get('model_theorem'));m,t=new.get(n,(None,None));added=m in accepted if m else False
 rows.append({**r,'model_context_available':before or added,'resume15_model_module':m if added else None,'resume15_model_theorem':t if added else None,'native_status':'OPEN','native_detail':remaining[n],'new_fully_composed_own1_bound':False})
assert len(rows)==36
(O/'link-status.json').write_text(json.dumps(rows,indent=2)+'\n')
model_count=sum(r['model_context_available']for r in rows)
coverage=dict(conservative_reachable_candidates=79,bound_bodies=41,reclassification_bound=40,reclassification_label='reclassification within existing Charon/Aeneas tool trust (owner fifth amendment)',own1_bound=1,new_own1_bound=0,changed_function_links=36,changed_function_model_context_instances=model_count,changed_function_complete_native_associations=0,exact_reachability_certified=False,excluded_peer_scope=['std/dependency catalogue','D188','deployed matrix-state association'])
(O/'coverage.json').write_text(json.dumps(coverage,indent=2)+'\n')
s='''# D500 V244 resume15 per-function status

**Runjoin op227 is not discharged. Target not yet established.** No endpoint premise or T field changed. V370 / pending owner D381,D386, the simulator and observer standing are retained.

Coverage: **79 conservative reachable candidates / 41 BOUND = 40 reclassification-bound + 1 own-1**, unchanged. Exact deployed reachability is uncertified; no pruning. The reclassification label is “reclassification within existing Charon/Aeneas tool trust (owner fifth amendment)”.

'''+f'Model/context instances: **{model_count}/36**. Complete changed-function native/source/dependency associations: **0/36**. A source-shaped model equality is not promoted to an actual deployed source binding; its pointer, primitive and callee associations remain explicit. The concrete standard/dependency catalogue, D188 and deployed matrix association belong to pv-b3q and were not worked here.\n\n| Function | Model/context | Native association / exact remaining obligation |\n|---|---|---|\n'
for r in rows:s+=f"| {r['function']} | {'AVAILABLE' if r['model_context_available'] else 'OPEN'} | **OPEN** — {r['native_detail']} |\n"
s+='''
The fields/Vec caller and terminal wrapper are separate from these 36 links. Their new proofs are model/caller composition; neither the actual allocator/std source association nor the deployed op227 implementation is supplied by choosing a model installation. See RESIDUALS.md and receipt-index.json. Failed modules and uncompiled drafts earn no credit.
'''
(O/'GROUP-STATUS.md').write_text(s)
print(json.dumps(coverage))
