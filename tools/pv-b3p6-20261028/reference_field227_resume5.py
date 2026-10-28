"""Owned fixed-arity projection helpers with unchanged arithmetic order."""
from pathlib import Path
import hashlib,json
P=Path('tools/pv-b3p6-20261028/v244');s=(P/'host_terminal_field.rs').read_text()
s+='''
pub(crate) fn qm31_sum_products3_prepared(left:&[PreparedQm31Multiplier;3],right:&[QM31;3])->QM31 {
    let mut sums=[[0u64;3];3];
'''
for index in range(3):
 s+=f'''    {{ let index={index}usize;
    let right_sum=right[index].c0.add(right[index].c1);
    let right_components=[
        [right[index].c0.a,right[index].c0.b,right[index].c0.a.add(right[index].c0.b)],
        [right[index].c1.a,right[index].c1.b,right[index].c1.a.add(right[index].c1.b)],
        [right_sum.a,right_sum.b,right_sum.a.add(right_sum.b)]];
'''
 for component in range(3):
  for channel in range(3):s+=f'    sums[{component}][{channel}]+=left[index].components[{component}][{channel}].0 as u64 * right_components[{component}][{channel}].0 as u64;\n'
 s+='    }\n'
s+='''    let m0=reconstruct_component(sums[0]);
    let m1=reconstruct_component(sums[1]);
    let m2=reconstruct_component(sums[2]);
    QM31{c0:m0.add(cm31_mul_r(m1)),c1:m2.sub(m0).sub(m1)}
}
pub(crate) fn qm31_m31_dot(weights:&[QM31;7],values:&[M31;7])->QM31 {
    let mut sums=[0u64;4];
'''
for begin,end in [(0,4),(4,7)]:
 s+='    { let mut raw=[0u64;4];\n'
 for index in range(begin,end):
  s+=f'    {{ let value=values[{index}].0 as u64; let weight=weights[{index}];\n'
  for k,field in enumerate(['c0.a','c0.b','c1.a','c1.b']):s+=f'    raw[{k}]+=weight.{field}.0 as u64 *value;\n'
  s+='    }\n'
 for k in range(4):s+=f'    sums[{k}]+=M31::reduce_u64(raw[{k}]).0 as u64;\n'
 s+='    }\n'
s+='''    QM31{c0:CM31::new(M31::reduce_u64(sums[0]),M31::reduce_u64(sums[1])),c1:CM31::new(M31::reduce_u64(sums[2]),M31::reduce_u64(sums[3]))}
}
'''
(P/'reference_field.rs').write_text(s)
Path('evidence/pv-b3p6-20261028/reference-field227-resume5.json').write_text(json.dumps(dict(base_sha256=hashlib.sha256((P/'host_terminal_field.rs').read_bytes()).hexdigest(),reference_sha256=hashlib.sha256(s.encode()).hexdigest(),scope='fixed3 prepared sum, fixed7 QM31/M31 dot, closure-free host-field helpers',arithmetic_order='3x3x3 prepared accumulation and two dot chunks [0..4), [4..7), each raw four-limb accumulation and reduction preserved; no reassociation',law_outstanding=True),indent=2)+'\n')
