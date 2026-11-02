"""Whole-body source binding for the three-product prepared field helper."""
from pathlib import Path
import json,hashlib
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
ns={};exec(compile(Path('tools/pv-b3p6-20261028/std_resolve_d540.py').read_text().split('indices={}')[0],'<parser>','exec'),ns)
tokens,index=ns['tokens'],ns['index']
def syntax(s):
 t=tokens(s)
 return [x for i,x in enumerate(t) if not(x==',' and i+1<len(t) and t[i+1]in [']','}'])]
p=Path('crates/aspis-core/src/field.rs');q=Path('tools/pv-b3p6-20261028/v244/reference_field.rs')
assert sha(p)==json.loads((D/'resume17/deployed-source-pins.json').read_text())[str(p)]
a=next(x for x in index(p.read_text())if x['name']=='qm31_sum_products3_prepared');b=next(x for x in index(p.read_text())if x['name']=='qm31_from_karatsuba_channel_sums')
channels='''let right_sum=right[index].c0.add(right[index].c1);let right_components=[[right[index].c0.a,right[index].c0.b,right[index].c0.a.add(right[index].c0.b)],[right[index].c1.a,right[index].c1.b,right[index].c1.a.add(right[index].c1.b)],[right_sum.a,right_sum.b,right_sum.a.add(right_sum.b)]];'''
expected='{let mut sums=[[0u64;3];3];for index in 0..3 {'+channels+'''for component in 0..3 {for channel in 0..3 {sums[component][channel]+=left[index].components[component][channel].0 as u64 *right_components[component][channel].0 as u64;}}}qm31_from_karatsuba_channel_sums(sums)}'''
assert syntax(a['body'])==syntax(expected)
ref=next(x for x in index(q.read_text())if x['name']=='accumulate_prepared227')
expanded='{'+channels.replace('right[index]','right')+''.join(f'sums[{i}][{j}]+=left.components[{i}][{j}].0 as u64 *right_components[{i}][{j}].0 as u64;'for i in range(3)for j in range(3))+'sums}'
assert syntax(ref['body'])==syntax(expanded)
reconstruct='''{let reconstruct=|channels:[u64;3]|{let m0=M31::reduce_u64(channels[0]);let m1=M31::reduce_u64(channels[1]);let m2=M31::reduce_u64(channels[2]);CM31{a:m0.sub(m1),b:m2.sub(m0).sub(m1),}};let m0=reconstruct(sums[0]);let m1=reconstruct(sums[1]);let m2=reconstruct(sums[2]);QM31{c0:m0.add(mul_by_r(m1)),c1:m2.sub(m0).sub(m1),}}'''
assert tokens(b['body'])==tokens(reconstruct)
# Complete private payload layout; M31 is transparent u32, not a canonical subtype.
assert tokens('struct PreparedQm31Multiplier {components:[[M31;3];3],}') in [tokens('struct PreparedQm31Multiplier '+p.read_text().split('pub struct PreparedQm31Multiplier',1)[1].split('\n\n',1)[0])]
assert 'pub struct M31(pub u32);' in p.read_text()
rot=next(x for x in index(p.read_text())if x['name']=='mul_by_r')
assert tokens(rot['body'])==tokens('{CM31{a:x.a.double().sub(x.b),b:x.a.add(x.b.double()),}}')
steps=[
 ('sums=[[0u64;3];3]','native_prepared14 initial','Exact 3x3 zero matrix, no canonicality condition.'),
 ('for index in0..3','range_loop13 native_product_term14','range_loop_binding13/three_loop12 enumerate0,1,2 in order. All source input reads in3. Hoisted immutable left[index] read is total on precisely these indices and cannot affect the preceding right field operations.'),
 ('right_sum and right_components','source_accumulate13','All four field calls and three row constructors have identical order and operands, checked against complete source tokens. Repeated immutable right[index] reads are pure bounded reads; no borrowed write aliases inputs.'),
 ('for component0..3,channel0..3','source_nested13/source_component13/source_channel12','Ordered lexicographic nine cells. Complete reference accumulator tokens equal the generated unrolling. Every u32 widens to u64, multiply wraps, then add wraps exactly as release. No algebraic reassociation or canonicality premise.'),
 ('sums[component][channel] += product','matrix_cell/matrix_cell_result','Read original row and old cell; borrow row, update selected channel, apply back(updated) to the full outer matrix. Each result feeds the next cell, row, and product. Every nested write is retained; no discarded backward continuation.'),
 ('qm31_from_karatsuba_channel_sums','source_channel_reconstruct13','Read rows0,1,2; invoke reconstruct_call_once13 in order, with exact reduce_u64 calls0,1,2 and same two CM31 fields. Closure immutable captures empty; FnOnce/drop lowering stays V370. Then mul_by_r, add, sub, sub in order, all return complete Result.'),
 ('PreparedQm31Multiplier payload','NativePrepared14/from_reference14/to_reference14','Single components:[[M31;3];3] field checked; M31 public raw u32. Conversion preserves all nine raw limbs. prepared_array_roundtrip550 establishes lossless nominal array transport; no constructor invariant assumed.'),
 ('mul_by_r vs cm31_mul_r','same field-level expression tree','Exact doubled/subtracted/added coordinates checked above. CM31::new(a,b) is the unchanged two-field constructor; no additional arithmetic or restriction.')]
x=dict(function='qm31_sum_products3_prepared',source=dict(path=str(p),sha256=sha(p),item=a,whole_body_tokens_checked=True),support=[b,rot],reference=dict(path=str(q),sha256=sha(q),accumulator=ref,all_nine_cells_checked=True),source_steps=[dict(source=s,model=m,argument=v)for s,m,v in steps],interpreter='prepared_source550 / native_prepared14',theorem='PV_B3P_Association550227.prepared_source_link550',domain='all raw nine-u32 prepared payloads and three raw QM31 values; no canonicality narrowing',route='own-1 structural argument + complete-Result Lean equality',D188='all27 cell writes retain inner row and outer matrix restoration; local indexed mutation only',feature_profile='ct-host-prover resolved reference graph recorded by N79168; deployed field items have no cfg/cfg!; release wrapping and debug assertions off',retained='whole std source catalogue, D188 differential/matrix and callback, V370/D381/D386; no endpoint premise or T change',status='pending new proof and exact reference replay; no credit yet')
(R/'PREPARED-SOURCE-D550.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps(dict(bodies=1,cells_per_product=9,products=3)))
