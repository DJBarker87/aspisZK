"""Inventory exact source/owned differences without claiming semantic closure.
Complete token spans and every diff hunk are retained per assigned function.
The native implementation catalogue is intentionally left to pv-b3q.
"""
from pathlib import Path
import json,hashlib,difflib,re,sys
D=Path('evidence/pv-b3p6-20261028');O=D/'resume15';I=json.loads((D/'resume9/body-inventory.json').read_text());old=json.loads((D/'resume14/link-status.json').read_text());sha=lambda b:hashlib.sha256(b).hexdigest()
for f in I['files']:
 for k in ['source','owned']:assert sha(Path(f[k]).read_bytes())==f[k+'_sha256'],f[k]
 if f['family']!='poseidon':assert Path(f['source']).read_bytes()==Path('crates/aspis-r1-cost-probe/src',Path(f['source']).name).read_bytes()
plans={
 'full_round':['range 0..16: read state, read constants, add, pow5, whole-element write','external_linear_lazy once after all sixteen lane steps','return entire mutated state'],
 'full_round_packed':['range 0..16: read state, read constants, add, pow5, whole-element write','external_linear_packed once after all sixteen lane steps','return four packed values'],
 'full_round_m31_constants':['range 0..16: read state/constant; M31 add; restore c0.a write','read newly written element; pow5; whole-element write','external_linear_lazy once; return entire state'],
 'full_round_m31_constants_packed':['range 0..16: read state/constant; M31 add; restore c0.a write','read newly written element; pow5; whole-element write','external_linear_packed once; return packed result'],
 'leading_pair_packed':['copy openings.z; range 0..8: read state/xor12, add, write','external linear layer','read EXTERNAL_INITIAL[0], full M31 round','read EXTERNAL_INITIAL[1], packed full M31 round'],
 'reconstruct_10':['immutable initial view[9] read','index=9; while index>0: decrement before indexed read','receiver add(acc,acc), then read view[index], then second add','return acc; shared input and loan identity unchanged'],
 'equality_value':['read left[0], right[0], equality_factor','index=1; while index<left.len(): read left[index], right[index], factor, multiply product','increment once after each factor/product; return product','both shared input loans remain unchanged, aliasing allowed'],
 'add_digest_binding':['range 0..8: expected read; conditional tweak if right_tweak && lane+1==8','read prior output, opened[start+lane]; lift target; subtract; multiply; add','write output[lane]; retain every previous write'],
 'add_preweighted':['divide start by 4; compute (start+N-1)/4 with deployed wrapping','inclusive group traversal with four source macro slots','each slot checks source>=start && source<start+N before values[source-start]','read packed[group], pack lanes, add and write packed[group]','inclusive iterator exhaustion and actual call-domain bounds remain explicit'],
 'active_literal':['sum=ZERO, block=0; while block<64','read frozen ACTIVE_ROW_MASKS[block]; skip zero mask','read high[block]; sum mask over shared low; multiply and add','increment; retain mask domain caller obligation'],
 'pattern_values_literal':['initialize powers and power=lambda; while limb<16 store power then multiply by lambda','initialize fourteen results; while pattern_index<14 read frozen pattern','reset limb=0; test kinds[limb]==1 before columns/offsets/openings reads','convert U8 column to usize; lift offset; add, weight, sum','store result; increment outer counter'],
 'selector_mask_sum_16':['count_ones>8 chooses complement; bitwise complement branch retained','initialize ONE if complement, ZERO otherwise','while mask!=0: trailing_zeros cast; indexed read; sub/add chosen by complement','mask &= mask-1; zero return preserved; domain guard and intrinsic association explicit'],
 'sum_high':['immutable outer slice iteration in source order','copy each Range by value and traverse increasing inner indices','read selectors.high[block], add to sum; no writes to either loan','normal and early failure cleanup of both iterators remains catalogue obligation'],
 'public_digest_lanes':['zero output then anchor/nullifier/optional recipient/change bindings in order','range level 0..20; select empty-root/tweaked or frontier binding by index bit','after.next_root binding; bounded carry and conditional next_frontier binding','return output with all stores in order'],
 'internal_linear_lazy':['read old_zero limbs; zero four part sums','while lane=1..15: read lane; four ordered limb additions','construct full_sum; write zero lane using part_sum + P - old_zero','range lane=1..15: read lane/shift; construct limb output; write lane','return full state; no matrix-state/D188 discharge claimed'],
 'qm31_sum_products3_prepared':['zero 3x3 sums; range index=0..3','read right c0/c1; construct nine right components','range component=0..3 then channel=0..3: read left private stored component and right component','widen, multiply, read sum, wrapping add, write sum','reconstruct Karatsuba channel sums; deployed matrix association is pv-b3q-owned'],
 'evaluate_state_only_poseidon_oracle_projected':['read local[0]; fold local rows [1,9,10]; fold rows 2..=8','leading/full/internal evaluations in source order','map three weights to prepared multipliers; prepare block','four groups in increasing from_fn order: target and internal four-lane slices','pack; three target residuals; prepared sum-products; multiply prepared block'],
 'add_value_lanes':['three row selectors then range selector','three ten-cell loops produce 30 range constraints, then reconstruct and final three cells','33-cell mutable scaling loop then preweighted insertion at 49','two conservation terms then insertion at 82; retain partial-store and D188 obligations'],
 'occupancy_lanes_literal':['read occupied and inverse; construct one_minus; zero twelve outputs; both=input+output','write outputs 0,1,2 in order','range lane=0..8: read opened[2+lane], two products, write occupancy[3+lane]','construct final occupancy[11] in source order and store'],
 'interpolate_three_constant_columns':['zero sixteen outputs; lane=0','while lane<16: four component calls each repeating three weight and three column reads','construct c0, then c1, then QM31; write output[lane]; increment','all repeated reads bounded; immutable source read caching proved separately'],
 'absorption_lanes_literal':['source macro while lane<16 from zero output','branch lane<2, lane<RATE, or remaining; additions select blocks','multiply low*blocks before opening read, then second product','write output[lane]; increment; bounded-read commutation proved separately'],
 'path_lanes_literal':['read bit; zero seventeen outputs; construct and write path[0]','range lane=0..8: read current; ONE-bit subtraction, left residual and first store','repeat selector*bit multiplication; right residual and second store','owned CSE of ONE-bit and selector*bit is justified by successful-result witnesses'],
}
plans.update({
 'add_path_lanes':['sum ranges [57,63); add low indices 1,5,9,13 in source order; multiply','deployed cfg selects the literal/factored path callee','insert the seventeen path lanes at start 32'],
 'add_schedule_lanes':['semantic_initial_and_absorption returns the ordered pair','insert initial at 0; retain resulting packed state','insert absorption at 16 using that state'],
 'composition_parts':['match withdrawal_amount and reject zero or >=2^30','validate_transition with exact Rust error propagation','select three opening rows, then mask-only columns','boxed selector constructor; projected Poseidon then semantic packed','copy evaluator then prepare theta','reverse semantic Horner loop, then reverse Poseidon Horner loop','return composition/opening/mask/G/H1/copy-active tuple'],
 'poseidon_selectors':['sum high range [0,57)','copy low array without changing the source loan','construct StateOnlyPoseidonSelectors {block,local}'],
 'semantic_initial_and_absorption':['sum node ranges [4,25),[33,57); read fixed high selectors','variant selector match; construct full/rate selectors and prepared multipliers','sixteen-lane initialization macro chooses full_or_rate for lane<RATE','domain and length corrections at RATE and RATE+1','construct private/common chunk selectors','deployed cfg chooses absorption callee; return ordered pair'],
 'semantic_packed':['zero 24 packed lanes','schedule, path, value and occupancy mutations in order','deployed cfg chooses public-digest insertion at 84 or packed-digest two stores','asset residual and three asset selector products','withdrawal unwrap_or/is_some and selected amount residual','variant scalar lanes; insertion at 92; return full packed array'],
 'validate_transition':['copy live/after shared references','short-circuit pool/domain/sequence/capacity/checked_add tests; Err on any mismatch','bounded carry; range level 0..20','continue exactly at level==carry && carry<20','choose empty root or source frontier by carry/index bit','compare after frontier; Err on mismatch; final Ok unit'],
 'qm31_m31_dot':['assert equal slice lengths; <=4 branch uses a single raw accumulator','actual caller has two seven-element slices; assert holds and <=4 branch is false','StepBy(4) gives starts 0 and 4; end=min(start+4,7)','per term read M31 and QM31; widen, multiply, wrapping add/store all four channels','reduce each chunk and wrapping-add reduced channels to sums','final four reductions and ordered CM31/QM31 construction'],
 'at_point':['expand first six point coordinates to 64 weights','source constant selects 57 high blocks; increasing copied fold from ZERO','expand last four point coordinates to sixteen local weights','construct block/local; preserve corrected legacy-layout and constructor-native obligations'],
 'expand':['release removes debug_assert; initialize ZERO weights then weights[0]=ONE','immutable coordinate iteration; prepare each coordinate','reverse index range 0..len; read parent before either child store','write weights[2*index]=parent-right, then weights[2*index+1]=right','double len after each coordinate; return full array'],
 'external_linear_lazy':['four groups: snapshot four inputs before any group output store','map extension limbs; four output/limb expressions, unreachable arm excluded by output<4','store all local group outputs','construct four column sums from the resulting full state','sixteen-lane loop adds matching column sum to each limb and stores reconstructed extension'],
 'external_linear_packed':['four groups: snapshot four inputs, external_local_packed, store group result','add four local packed values to ZERO in order','map each local packed value to value+sum'],
 'external_local_packed_raw':['map four extension inputs to raw limbs','four-by-four from_fn computes source match for outputs 0..3','execute all_local_limbs_bounded loop; debug assertions have no release effect','evaluate the four source packed integer expressions with wrapping arithmetic','release omits final debug assertions; return four raw channels'],
 'interpolated_internal_pair':['ROWS=[2,3,4,5,6,7,8]; array maps retain order','read seven local weights and seven even/odd INTERNAL constants','dot(weights,even) then dot(weights,odd)','internal_round(state,even) then internal_round(result,odd)'],
})

models={
 'full_round':['PV_B3P_NativeRoundQPlain15227'], 'full_round_packed':['PV_B3P_NativeRoundQPacked15227'],
 'full_round_m31_constants':['PV_B3P_NativeRoundMPlain15227'],'full_round_m31_constants_packed':['PV_B3P_NativeRoundMPacked15227'],
 'leading_pair_packed':['PV_B3P_NativeLeading15227'],'add_digest_binding':['PV_B3P_NativeDigestStore15227'],
 'add_preweighted':['PV_B3P_NativePreweighted15227'],'active_literal':['PV_B3P_NativeActive15227'],
 'pattern_values_literal':['PV_B3P_NativePattern15227'],'public_digest_lanes':['PV_B3P_NativePublicDigest15227'],
 'sum_high':['PV_B3P_NativeSumHigh15227'],'internal_linear_lazy':['PV_B3P_NativeInternal15227'],
 'reconstruct_10':['PV_B3P_NativeSharedRead15227','PV_B3P_ReconstructNative14227'],
 'equality_value':['PV_B3P_NativeSharedRead15227','PV_B3P_EqualityNative14227'],
 'selector_mask_sum_16':['PV_B3P_NativeMaskSafety15227','PV_B3P_MaskNative14227'],
 'evaluate_state_only_poseidon_oracle_projected':['PV_B3P_NativeProjected15227'],
 'occupancy_lanes_literal':['PV_B3P_NativeOccupancy15227'],
 'interpolate_three_constant_columns':['PV_B3P_InterpolationSource15227'],
 'absorption_lanes_literal':['PV_B3P_AbsorptionSource15227'],
 'path_lanes_literal':['PV_B3P_NativePath15227']}
models.update({
 'poseidon_selectors':['PV_B3P_PoseidonSelectorCaller15227'],
 'add_schedule_lanes':['PV_B3P_ScheduleCaller15227'],
})

receipt_path=O/'receipt-index.json'
latest={}
if receipt_path.exists():
 for receipt in sorted(json.loads(receipt_path.read_text()),key=lambda r:r['attempt']):latest[receipt['module']]=receipt
rows=[]
for r in old:
 b=I['bodies'][r['index']];assert b['key'].split('#')[0]==r['function'];name=r['function'];f=next(f for f in I['files']if f['family']==b['family'])
 a=(b.get('source') or {}).get('tokens',[]);z=(b.get('owned') or {}).get('tokens',[])
 d=list(difflib.SequenceMatcher(a=a,b=z,autojunk=False).get_opcodes());diffs=[dict(tag=t,source_begin=i,source_end=j,owned_begin=k,owned_end=l,source_tokens=a[i:j],owned_tokens=z[k:l])for t,i,j,k,l in d if t!='equal']
 # Every token on each side appears in one and only one matching/differing span.
 assert sum(j-i for _,i,j,_,_ in d)==len(a)
 assert sum(l-k for _,_,_,k,l in d)==len(z)
 bindings=[]
 for m in models.get(name,[]):
  p=D/'lean'/(m+'.lean');raw=p.read_bytes();bindings.append(dict(module=m,source_sha256=sha(raw),declarations=re.findall(r'^(?:theorem|def) (\S+)',raw.decode(),re.M),compile_status=('COMPILED_MODEL_ONLY; native association OPEN' if m in latest and latest[m]['exit']==0 and latest[m]['source_sha256']==sha(raw) else 'UNCOMPILED_OR_FAILED_DRAFT; no credit')))
 rows.append(dict(function=name,group=b['family'],inventory_index=r['index'],source=dict(path=f['source'],file_sha256=f['source_sha256'],begin_line=(b.get('source') or {}).get('line'),end_line=(b.get('source') or {}).get('end_line'),body_token_sha256=sha('\0'.join(a).encode()),tokens=a),owned=dict(path=f['owned'],file_sha256=f['owned_sha256'],body_token_sha256=sha('\0'.join(z).encode())),complete_difference_partition=diffs,source_steps=plans.get(name,[]),new_model_bindings=bindings,body_native_status='OPEN until every listed source transformation and callee association is verified',dependency_catalogue_owner='pv-b3q / codex/pv-b3q-20261029 / PV_B3Q_',machine_boundary='V370; pending owner D381,D386 retained',new_complete_own1_credit=False))
x=dict(scope='36 assigned changed functions only',functions=rows,excluded=['std/dependency catalogue','D188','deployed matrix-state association'],method='Complete token-difference inventory plus explicit source-step dossiers. This file alone is NOT a source interpreter or semantic proof.',fully_composed_new_bound=0)
p=O/'source-association-dossiers.json'
if '--check'in sys.argv:assert json.loads(p.read_text())==x
else:p.write_text(json.dumps(x,indent=2)+'\n')
print(json.dumps(dict(functions=len(rows),step_dossiers=sum(bool(r['source_steps'])for r in rows),full_body_credit=0)))
