from pathlib import Path
R=Path.cwd();p=R/'crates/aspis-prover/src/host_arithmetic.rs';s=p.read_text();s=s.replace('    qm31_sum_products3, PreparedQm31Multiplier, CM31, M31, QM31,','    CM31, M31, QM31,')
# rustfmt may use a single-line import; remove names in either shape.
s=s.replace('qm31_sum_products3, ', '').replace('PreparedQm31Multiplier, ', '')
helpers='''
// Private prepared carrier copied from field.rs. Explicit functions replace
// the two noncapturing closures whose precise Drop blocks fail preflight.
#[derive(Clone,Copy)]
struct PreparedQm31Multiplier {components:[[M31;3];3]}
#[inline(always)]
fn prepare_component(component:CM31)->[M31;3]{[component.a,component.b,component.a.add(component.b)]}
#[inline(always)]
fn prepared_component_mul(left:[M31;3],right:CM31)->CM31{
 let m0=left[0].mul(right.a);let m1=left[1].mul(right.b);let m2=left[2].mul(right.a.add(right.b));
 CM31{a:m0.sub(m1),b:m2.sub(m0).sub(m1)}
}
impl PreparedQm31Multiplier {
 #[inline(always)] fn new(value:QM31)->Self{Self{components:[prepare_component(value.c0),prepare_component(value.c1),prepare_component(value.c0.add(value.c1))]}}
 #[inline(always)] fn mul(self,rhs:QM31)->QM31{
  let m0=prepared_component_mul(self.components[0],rhs.c0);let m1=prepared_component_mul(self.components[1],rhs.c1);let m2=prepared_component_mul(self.components[2],rhs.c0.add(rhs.c1));
  QM31{c0:m0.add(cm31_mul_r(m1)),c1:m2.sub(m0).sub(m1)}
 }
}
#[inline(always)]
fn reconstruct_component(channels:[u64;3])->CM31{
 let m0=M31::reduce_u64(channels[0]);let m1=M31::reduce_u64(channels[1]);let m2=M31::reduce_u64(channels[2]);CM31{a:m0.sub(m1),b:m2.sub(m0).sub(m1)}
}
#[inline(always)]
fn reconstruct_channels(sums:[[u64;3];3])->QM31{
 let m0=reconstruct_component(sums[0]);let m1=reconstruct_component(sums[1]);let m2=reconstruct_component(sums[2]);QM31{c0:m0.add(cm31_mul_r(m1)),c1:m2.sub(m0).sub(m1)}
}
#[inline(always)]
fn accumulate_channels(mut sums:[[u64;3];3],left:QM31,right:QM31)->[[u64;3];3]{
 let left_sum=left.c0.add(left.c1);let right_sum=right.c0.add(right.c1);
 let a=[[left.c0.a,left.c0.b,left.c0.a.add(left.c0.b)],[left.c1.a,left.c1.b,left.c1.a.add(left.c1.b)],[left_sum.a,left_sum.b,left_sum.a.add(left_sum.b)]];
 let b=[[right.c0.a,right.c0.b,right.c0.a.add(right.c0.b)],[right.c1.a,right.c1.b,right.c1.a.add(right.c1.b)],[right_sum.a,right_sum.b,right_sum.a.add(right_sum.b)]];
'''+''.join(f' sums[{i}][{j}] += a[{i}][{j}].0 as u64 * b[{i}][{j}].0 as u64;\n' for i in range(3) for j in range(3))+''' sums
}
#[inline(always)]
fn qm31_sum_products3(left:[QM31;3],right:[QM31;3])->QM31{
 let sums=accumulate_channels([[0u64;3];3],left[0],right[0]);
 let sums=accumulate_channels(sums,left[1],right[1]);
 let sums=accumulate_channels(sums,left[2],right[2]);reconstruct_channels(sums)
}
'''
s+='\n'+helpers;p.write_text(s)
