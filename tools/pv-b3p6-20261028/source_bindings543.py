"""own-1 statements for four refused bodies; frozen source and named laws.
Structural arguments, not machine proofs. No concrete field evaluation.
"""
from pathlib import Path
import json,hashlib,sys
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
ns={};exec(compile(Path('tools/pv-b3p6-20261028/std_resolve_d540.py').read_text().split('indices={}')[0],'<parser>','exec'),ns)
tokens,index=ns['tokens'],ns['index']
def syntax_tokens(s):
 t=tokens(s);return [x for i,x in enumerate(t)if not(x==','and i+1<len(t)and t[i+1]in [')','}',']'])]
pins=json.loads((D/'resume17/deployed-source-pins.json').read_text())
def body(path,name,expected):
 p=Path(path);assert sha(p)==pins[path]
 a=next(a for a in index(p.read_text())if a['name']==name)
 assert syntax_tokens(a['body'])==syntax_tokens(expected),name
 return dict(path=path,sha256=sha(p),item=a,whole_body_token_check=True,syntax_normalization="optional trailing commas only")
terminal='crates/aspis-r1-cost-probe/src/host_terminal.rs';poseidon='crates/aspis-statement/src/state_only_poseidon.rs'
rows=[]
def add(name,src,steps,laws,domain,stores):
 rows.append(dict(function=name,source=src,source_steps=[dict(source=a,model=b,argument=c)for a,b,c in steps],compiled_named_laws=laws,domain=domain,stores=stores,route='own-1 script-checked structural source binding + named complete-Result Lean equality',evidence_class='structural argument; Lean equality concerns the exact stated source interpreter, not machine-code preservation',D188='Every local indexed assignment retains its mutable loan restoration via source_store_update543/source_store_continuation543; this is an own-1 interpreter, not an unsupported extraction. No discarded mutable backward function is accepted.',retained='Field source rows and standard/dependency closure remain named separately. Compiler lowering, intrinsics, copy/drop and source-to-machine V370 / D381,D386 retained. No endpoint or T change.'))
src=body(terminal,'equality_value','''{let mut product=equality_factor(left[0],right[0]);let mut index=1usize;while index<left.len(){product=product.mul(equality_factor(left[index],right[index]));index+=1;}product}''')
add('equality_value',src,[
 ('two immutable &[QM31;10] loans','Shared14 EqualityInput14 / equality_native14','Retain both identities; allow identical/overlapping loans. Neither source nor model writes inputs, dereferences arbitrary addresses, compares addresses, or inspects outside state.'),
 ('equality_factor(left[0],right[0])','two Array.index_usize then exact reference_terminal.equality_factor','Source left read precedes right read and opaque field call. Both indices 0<10; index_value records same contents. equality_factor is the token-identical helper from the pinned source/copy; no arithmetic reassociation.'),
 ('index=1; while index<left.len()','source_equality_loop, usize_body equality_step 10','Fixed array len is10 independent of values. For each index1..9 read left then right, evaluate same factor and multiply old product on the left. Increment only after storing product. No integer overflow because index<=10. equality_loop_binding/usize_loop_plan covers precisely nine steps, preserving Result failures/divergence.'),
 ('return product; cleanup shared inputs','equality_native_continuation14','No custom Drop, allocation or mutable restoration. Immutable Copy field/array values retain identical order; compiler copy/drop lowering V370. Arbitrary continuation equality retains the resulting value.')],['PV_B3P_Loans14227.equality_native_binding14','PV_B3P_Loans14227.equality_native_continuation14','PV_B3P_Binding9227.equality_body_binding'],'every pair of valid shared arrays, including aliases and every raw field representation',0)
src=body(terminal,'occupancy_lanes_literal','''{let occupied=opened[0];let inverse=opened[1];let one_minus=QM31::ONE.sub(occupied);let mut occupancy=[QM31::ZERO;12];let both=input_occupancy.add(output_occupancy);occupancy[0]=both.mul(occupied.mul(occupied.sub(QM31::ONE)));occupancy[1]=both.mul(opened[9].mul(inverse).sub(occupied));occupancy[2]=both.mul(one_minus.mul(inverse));for lane in 0..DIGEST_ELEMS {occupancy[3+lane]=both.mul(one_minus.mul(opened[2+lane]));}occupancy[11]=input_occupancy.mul(opened[10].mul(one_minus)).add(output_occupancy.mul(occupied.sub(lift_m31(expected_output))));occupancy}''')
add('occupancy_lanes_literal',src,[
 ('read opened[0], opened[1]; ONE.sub(occupied)','native_occupancy15 prefix','Same read and field-call order. Bounds0,1<16 are value-independent. Shared opened is never mutated; possible external aliases are immutable.'),
 ('[ZERO;12], both=input.add(output)','Array.repeat12 ZERO, exact QM31.add','QM31 and all fields are Copy and have no custom destructor; source array-repeat lowering V370, not an ordinary std function silently omitted. No allocation or address-dependent control.'),
 ('stores occupancy[0], [1], [2] in source order','native_occupancy15 three Array.update binds','Every operand and evaluation order is the exact source expression; each nested field call remains opaque. source_store_update543 binds direct local element assignment; continuation lemma applies the back function before later stores. All fixed indices<12 and opened[9]<16.'),
 ('for lane in 0..8; occupancy[3+lane]=both.mul(one_minus.mul(opened[2+lane]))','occupancy_step15 / range_loop13','Range source has same IntoIterator/next/spec_next/Step bodies captured in SUM-SOURCE-BINDING-D542 and direct range_next_extraction17; cursor increments before body. occupancy_indices543 proves read2+lane<16 and target3+lane<12. Both scalar additions and range successor fit usize. The full Array.update state is threaded into each next step, never discarded.'),
 ('final occupancy[11] expression then return','occupancy_finish15','Read opened[10], multiply opened10*one_minus, multiply input; then lift expected_output, subtract from occupied, multiply output; finally add and store11. Exact lift_m31 helper source, same CM31/QM31 constructors; no arithmetic regrouping. Every cell0..11 written once, local array ownership returned; source_store_continuation543 retains final write.')],['PV_B3P_Native15227.native_occupancy_binding15','PV_B3P_Association543227.occupancy_indices543','PV_B3P_Association543227.source_store_continuation543'],'all raw field values, expected_output words and valid opened[16]; no canonicality premise',12)
src=body(terminal,'poseidon_selectors','''{StateOnlyPoseidonSelectors{block:sum_high(selectors,&[0..57]),local:selectors.low}}''')
add('poseidon_selectors',src,[
 ('immutable &Selectors and singleton Range slice','native_poseidon_selectors15 / source_sum_ranges13 [(0,57)]','Selectors has exactly high[64],low[16]. The source/copy carrier map preserves both whole arrays; no assumed invariant. Slice preserves singleton range0..57, shared loan identity and order. No heap allocation.'),
 ('block: sum_high(selectors,&[0..57])','previously source-bound source_sum_ranges13','D542 own-1 total sum dossier binds the actual callee, not only a model alias. Same57 left-fold additions. sum_ranges_binding13/native_sum_high_binding15 include range/drop and arbitrary raw fields. This body introduces no independent arithmetic.'),
 ('local: selectors.low and constructor','ok {block, local:=selectors.low}','Exact immutable Copy of16 field elements, no writes, custom destructor or effects. Carrier fields/order agree with the same-origin PoseidonSelectors extraction. The field constructor is evaluated after block and returns both values intact.')],['PV_B3P_Native15227.native_poseidon_selectors_binding15','PV_B3P_Binding13227.sum_ranges_binding13','PV_B3P_Native15227.native_sum_high_binding15'],'all high[64],low[16] selector arrays; no canonicality premise',0)
parts=[]
for outer in ['c0','c1']:
 limbs=[]
 for inner in ['a','b']:
  limbs.append('interpolate_three_constant_limb('+','.join([f'weights[{i}].{outer}.{inner}.0'for i in range(3)]+[f'column{i}[lane]'for i in range(3)])+')')
 parts.append(outer+':CM31::new('+','.join(limbs)+')')
expected='{let mut output=[QM31::ZERO;POSEIDON2_WIDTH];let mut lane=0usize;while lane<POSEIDON2_WIDTH {output[lane]=QM31{'+','.join(parts)+',};lane+=1;}output}'
src=body(poseidon,'interpolate_three_constant_columns',expected)
add('interpolate_three_constant_columns',src,[
 ('owned weights[3], column0/1/2[16]; output[16]=ZERO; lane=0','interpolation_source15','Same fixed-size value carrier. No mutable input reference, external read, allocation or custom Drop. Repeat semantics is compiler Copy lowering under V370.'),
 ('while lane<16; four component expressions in c0.a,c0.b,c1.a,c1.b order','interpolation_native_value15 / interpolation_native_limb15','For each component independently read weights0,1,2 then column0/1/2 at lane, exactly as source. Do not cache or reorder reads. index_value proves weights and lane accesses succeed; native_value_binding15 only factors successful immutable reads. CM31::new and QM31 field constructors remain in exact source order.'),
 ('each interpolate_three_constant_limb call','same extracted reference_poseidon.interpolate_three_constant_limb','The source/copy helper is token-identical under deployed ct-host-prover features, pinned in source grammar/dossiers. All u64 multiplications/additions retain release wrapping operation order; no canonical-field or non-overflow claim is substituted. M31::reduce_u64 is the same frozen field item, separately bound in field cone.'),
 ('output[lane]=value; lane+=1','interpolation_source_step15 Array.update; usize_body; interpolation_source_binding15','source_store_update543/source_store_continuation543 preserve every one of16 full-QM31 writes, including all four component limbs. On lane0..15 the destination is valid. Increment16 does not overflow. Terminal branch returns complete output. No mutable backward result is dropped.')],['PV_B3P_Native15227.interpolation_native_value_binding15','PV_B3P_Native15227.interpolation_source_step_binding15','PV_B3P_Native15227.interpolation_source_binding15','PV_B3P_Association543227.source_store_continuation543'],'every weights[3], columns[16] raw u32 representation, including wrap boundaries; no canonicality premise',16)
# Pin the actual helper bodies referenced in the structural map.
helpers=[]
for path,names in [(terminal,['equality_factor','lift_m31']),(poseidon,['interpolate_three_constant_limb'])]:
 for a in index(Path(path).read_text()):
  if a['name']in names:
   owned=Path('tools/pv-b3p6-20261028/v244')/('reference_terminal.rs'if path==terminal else'reference_poseidon.rs')
   candidate=next(v for v in index(owned.read_text())if v['name']==a['name'])
   assert syntax_tokens(a['body'])==syntax_tokens(candidate['body']),a['name']
   helpers.append(dict(path=path,sha256=sha(Path(path)),item=a,owned=str(owned),owned_sha256=sha(owned),owned_item=candidate,exact_body_token_identity=True))
assert len(helpers)==3
out=dict(rule='own-1 / k-prime route3',functions=rows,exact_helpers=helpers,std_range_binding='resume17/SUM-SOURCE-BINDING-D542.json; eight exact deployed ordinary std bodies; derived Clone/drop/intrinsics V370',primitive_binding='Fixed-array read/write and len are MIR primitive operations, not an omitted ordinary std Index implementation. Source bounds map to index_value; mutable back restoration maps to source_store_update543 and arbitrary continuation theorem. Their compiler/runtime implementation remains V370.',callee_binding='Same frozen project items on source and interpreter side, not axioms or arbitrary opaque functions. Local body equality is modulo the separately named dependency rows, as for the retained direct source associations. This does not assert whole source-cone closure.',coverage_status='pending ArrayInterface543227 and BodyLinks543227 compile/audit; only count after receipts',ordinary_std_unargued=[],native_tests='No changed release source/artifact; reuse existing finite validation only, never promote it to universal source proof')
(R/'LOCAL-SOURCE-BINDINGS-D543.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(dict(bodies=len(rows),explicit_helper_bodies=len(helpers),stores=sum(r['stores']for r in rows))))
