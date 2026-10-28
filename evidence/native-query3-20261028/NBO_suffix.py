from pathlib import Path
E=Path(__file__).resolve().parent
s=(E/'NBO_native.rs.txt').read_text()
s+='''
static mut NBO_ALPHA1:E=E::ZERO;
static mut NBO_LINE:E=E::ZERO;
static mut NBO_LINE_CALLS:usize=0;
fn NBO_line(alpha:E,values:[E;4],inverse:&[M31;5])->E {unsafe {
 NBO_LINE_CALLS+=1;let k=NBO_COORD;assert_eq!(alpha.to_limbs()[k],NBO_ALPHA1.to_limbs()[k]);
 assert_eq!(values[0].to_limbs()[k],NBO_VALUES[0].to_limbs()[k]);
 assert_eq!(values[1].to_limbs()[k],NBO_VALUES[1].to_limbs()[k]);
 assert_eq!(values[2].to_limbs()[k],NBO_VALUES[2].to_limbs()[k]);
 assert_eq!(values[3].to_limbs()[k],NBO_VALUES[3].to_limbs()[k]);
 assert_eq!(inverse[k%5],NBO_INV[k%5]);NBO_LINE}}
// Literal source continuation up to the node field-operation cut.
fn NBO_line_geometry(alpha:E,values:[E;4],inverse:&[M31;5],i:usize,geometry:&QueryGeometry)->(E,M31) {
 let folded=line_fold_with_inverses(alpha,values,inverse);
 crate::trace::value(10,2*i+1,folded);
 let z=geometry.line_z[i-geometry.start];
 (folded,z)
}
#[kani::proof]
#[kani::unwind(1024)]
#[kani::stub(crate::verifier::line_fold_with_inverses,NBO_line)]
fn NBO_line_geometry_routing() {
 let i:usize=kani::any();kani::assume(i<10);let start:usize=kani::any();kani::assume(start<=i);
 let k:usize=kani::any();kani::assume(k<8);let alpha=NBO_any_e();let line=NBO_any_e();
 let values=[NBO_any_e(),NBO_any_e(),NBO_any_e(),NBO_any_e()];
 let inverse=[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())];
 let zs:[u32;10]=kani::any();
 let geometry=QueryGeometry{start,inverses:Vec::new(),line_z:Vec::from([
 M31(zs[0]),M31(zs[1]),M31(zs[2]),M31(zs[3]),M31(zs[4]),M31(zs[5]),M31(zs[6]),M31(zs[7]),M31(zs[8]),M31(zs[9])])};
 unsafe{NBO_COORD=k;NBO_ALPHA1=alpha;NBO_LINE=line;NBO_VALUES=values;NBO_INV=inverse;}
 let(out,z)=NBO_line_geometry(alpha,values,&inverse,i,&geometry);
 assert_eq!(out.to_limbs()[k],line.to_limbs()[k]);assert_eq!(z.0,zs[i-start]);
 assert_eq!(geometry.start,start);assert_eq!(geometry.line_z.len(),10);
 unsafe{assert_eq!(NBO_LINE_CALLS,1);}
 kani::cover!(start==i);kani::cover!(i==9);kani::cover!(start<i);
}
// Counter/assignment cut after rhs and power have returned. All returned
// carriers are unconstrained here; their operations and domains remain explicit.
#[kani::proof]
#[kani::unwind(1024)]
fn NBO_tail_assignment() {
 let mut next:usize=kani::any();kani::assume(next<10);let mut terms:usize=kani::any();kani::assume(terms==next);
 let old=next;let mut rhs=NBO_any_e();let old_rhs=rhs;let returned_rhs=NBO_any_e();
 let mut power=K::ZERO;let returned_power=NBO_any_e().c0();let k:usize=kani::any();kani::assume(k<8);
 terms+=1;
 assert_eq!(rhs.to_limbs()[k],old_rhs.to_limbs()[k]);
 rhs=returned_rhs;crate::trace::value(11,next,rhs);
 power=returned_power;next+=1;
 assert_eq!(next,old+1);assert_eq!(terms,next);assert_eq!(rhs.to_limbs()[k],returned_rhs.to_limbs()[k]);
 let words=|q:K|[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0];assert_eq!(words(power)[k%4],words(returned_power)[k%4]);
 kani::cover!(old==0);kani::cover!(old==9);
}
'''
(E/'NBO_native.rs.txt').write_text(s)
