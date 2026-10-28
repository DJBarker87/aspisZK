from pathlib import Path
E=Path(__file__).resolve().parent;s=(E/'NBO_native.rs.txt').read_text()
s+='''
const _: ()=assert!(!cfg!(feature="prover"));
static mut NBO_SCALE_CALLS:usize=0;
static mut NBO_SCALE_X:[u32;3]=[0;3];static mut NBO_SCALE_Y:[u32;3]=[0;3];static mut NBO_SCALE_OUT:[u32;3]=[0;3];
fn NBO_scale_spec(x:M31,y:M31)->M31{
 assert!(x.0<2147483647);assert!(y.0<2147483647);let out:u32=kani::any();
 kani::assume(out as u64==(x.0 as u64*y.0 as u64)%2147483647);kani::assume(out<2147483647);
 unsafe{let i=NBO_SCALE_CALLS;assert!(i<3);NBO_SCALE_CALLS+=1;NBO_SCALE_X[i]=x.0;NBO_SCALE_Y[i]=y.0;NBO_SCALE_OUT[i]=out;}M31(out)
}
// Native pre-scalar cuts. Cases7/8 start AFTER the SAME c0/c1 scale calls:
// a,b are those returned canonical values, not the opening's original a,b.
fn NBO_coefficient_cut(which:u8,a:E,b:E,c:E,d:E,inverse:[M31;5])->(E,M31){
 let quarter=M31(536870912);let half=M31(1073741824);
 match which{
 0=>(a.add(b).add(c).add(d),quarter),
 1=>(a.sub(b).sub(c).add(d),quarter.mul(inverse[1])),
 2=>(a.add(b).sub(c).sub(d),quarter.mul(inverse[0])),
 3=>(a.sub(b).add(c).sub(d),quarter.mul(inverse[0]).mul(inverse[1])),
 4=>(a.add(b).sub(c).sub(d),quarter.mul(inverse[4])),
 5=>(a.sub(b),half.mul(inverse[2])),
 6=>(d.sub(c),half.mul(inverse[3])),
 7=>(a.add(b),half),
 _=>(a.sub(b),half.mul(inverse[4]))
 }
}
fn NBO_coefficient_case(which:u8){
 let a=NBO_any_e();let b=NBO_any_e();let c=NBO_any_e();let d=NBO_any_e();let k:usize=kani::any();kani::assume(k<8);
 let inv:[u32;5]=kani::any();kani::assume(inv[0]<2147483647);kani::assume(inv[1]<2147483647);kani::assume(inv[2]<2147483647);kani::assume(inv[3]<2147483647);kani::assume(inv[4]<2147483647);
 let(arg,scale)=NBO_coefficient_cut(which,a,b,c,d,[M31(inv[0]),M31(inv[1]),M31(inv[2]),M31(inv[3]),M31(inv[4])]);
 assert!(arg.to_limbs()[k]<2147483647);assert!(scale.0<2147483647);
 unsafe{
 let count=if which==0||which==7 {0}else if which==3 {2}else{1};assert_eq!(NBO_SCALE_CALLS,count);
 if count==0 {assert_eq!(scale.0,if which==0 {536870912}else{1073741824});}
 else {
 let constant=if which<5 {536870912}else{1073741824};assert_eq!(NBO_SCALE_X[0],constant);
 let slot=match which{1=>1,2|3=>0,4|8=>4,5=>2,_=>3};assert_eq!(NBO_SCALE_Y[0],inv[slot]);
 if count==2{assert_eq!(NBO_SCALE_X[1],NBO_SCALE_OUT[0]);assert_eq!(NBO_SCALE_Y[1],inv[1]);}
 assert_eq!(scale.0,NBO_SCALE_OUT[count-1]);
 }
 }
 kani::cover!(k==0);kani::cover!(k==7);
}
'''
for i,name in enumerate(['common_h0','circle_h1','circle_h2','circle_h3','line_h2','line_c0','line_c1','line_h1','line_h3']):
 s+='#[kani::proof]\n#[kani::unwind(4096)]\n#[kani::stub(aspis_core::field::M31::mul,NBO_scale_spec)]\nfn NBO_coeff_'+name+'(){NBO_coefficient_case('+str(i)+');}\n'
s+='''
// ONE Horner pre-multiply cut shared by all three source nesting sites.
fn NBO_horner_argument(alpha:E,h:E,previous_product:E)->(E,E){(alpha,h.add(previous_product))}
#[kani::proof]
#[kani::unwind(4096)]
fn NBO_horner_argument_cut(){
 let alpha=NBO_any_e();let h=NBO_any_e();let previous=NBO_any_e();let k:usize=kani::any();kani::assume(k<8);
 let(receiver,arg)=NBO_horner_argument(alpha,h,previous);
 assert_eq!(receiver.to_limbs()[k],alpha.to_limbs()[k]);assert!(arg.to_limbs()[k]<2147483647);
 kani::cover!(k==0);kani::cover!(k==7);
}
'''
(E/'NBO_native.rs.txt').write_text(s)
