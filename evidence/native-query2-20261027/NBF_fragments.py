from pathlib import Path
E=Path(__file__).resolve().parent
p=E/'NBF_harness.rs.txt'
assert 'fn NBF_fragment_case' not in p.read_text()
attrs='''#[kani::proof]
#[kani::unwind(9)]
#[kani::stub(aspis_core::field::M31::mul,NBF_field::m31)]
#[kani::stub(aspis_core::field::QM31::mul_m31,NBF_field::scalar)]
'''
s='''
fn NBF_scalar_result(group:usize)->E {
 unsafe {let a=NBF_field::SO[2*group];let b=NBF_field::SO[2*group+1];E::from_limbs([a[0],a[1],a[2],a[3],b[0],b[1],b[2],b[3]]).unwrap()}
}
// Literal native subexpressions after decomposition. All inputs are arbitrary
// canonical carriers; each field multiplication is a Lean-discharged stub.
fn NBF_fragment_case(which:u8) {
 let [a,b,c,d]=[NBF_fold_any_e(),NBF_fold_any_e(),NBF_fold_any_e(),NBF_fold_any_e()];
 let inv=NBF_fold_inverse();let ix=if which<4 {inv[0]} else {inv[2]};let iy=if which<4 {inv[1]} else {inv[3]};let iz=inv[4];let half=M31(1073741824);
 let k:usize=kani::any();kani::assume(k<8);
 let out=match which {
  0=>a.add(b).add(c).add(d).mul_m31(QUARTER),
  1=>a.sub(b).sub(c).add(d).mul_m31(QUARTER.mul(iy)),
  2=>a.add(b).sub(c).sub(d).mul_m31(QUARTER.mul(ix)),
  3=>a.sub(b).add(c).sub(d).mul_m31(QUARTER.mul(ix).mul(iy)),
  4=>a.add(b).sub(c).sub(d).mul_m31(QUARTER.mul(iz)),
  5=>a.sub(b).mul_m31(half.mul(ix)),
  6=>d.sub(c).mul_m31(half.mul(iy)),
  7=>{let c0=a.sub(b).mul_m31(half.mul(ix));let c1=d.sub(c).mul_m31(half.mul(iy));c0.add(c1).mul_m31(half)},
  _=>{let c0=a.sub(b).mul_m31(half.mul(ix));let c1=d.sub(c).mul_m31(half.mul(iy));c0.sub(c1).mul_m31(half.mul(iz))}
 };
 let group=if which<7 {0}else{2};
 let expected=match which {
  0=>a.add(b).add(c).add(d),1=>a.sub(b).sub(c).add(d),2|4=>a.add(b).sub(c).sub(d),
  3=>a.sub(b).add(c).sub(d),5=>a.sub(b),6=>d.sub(c),
  7=>NBF_scalar_result(0).add(NBF_scalar_result(1)),
  _=>NBF_scalar_result(0).sub(NBF_scalar_result(1))
 };
 unsafe {
 assert_eq!(NBF_field::SC,2*(group+1));
 assert_eq!(NBF_field::SX[2*group+k/4][k%4],expected.to_limbs()[k]);
 let scale=if which==0 {536870912} else if which==3 {NBF_field::MO[1]} else if which==7 {1073741824} else if which>=8 {NBF_field::MO[2]} else {NBF_field::MO[0]};
 assert_eq!(NBF_field::SY[2*group+k/4],scale);
 assert_eq!(out.to_limbs()[k],NBF_field::SO[2*group+k/4][k%4]);
 let muls=if which==0 {0} else if which==3||which==7 {2} else if which>=8 {3} else {1};
 assert_eq!(NBF_field::MC,muls);
 }
 kani::cover!(k==0);kani::cover!(k==7);
}
'''
for i,name in enumerate(['circle_h0','circle_h1','circle_h2','circle_h3','line_h2','line_c0','line_c1','line_h1','line_h3']):
 s+=attrs+f'fn NBF_{name}(){{NBF_fragment_case({i})}}\n'
p.write_text(p.read_text()+s)
