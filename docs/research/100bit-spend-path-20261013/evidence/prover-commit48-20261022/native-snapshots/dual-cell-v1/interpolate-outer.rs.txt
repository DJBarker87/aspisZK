mod outer_interpolation {
#[derive(Clone,Copy,Debug,PartialEq,Eq)] struct F(u32);
#[derive(Clone,Copy,Debug,PartialEq,Eq)] struct Call(u8,F,F);
static mut ANSWERS:[u32;64]=[0;64];
static mut CALLS:[Call;64]=[Call(0,F(0),F(0));64];
static mut NEXT:usize=0;
fn reset(answers:[u32;64]) {unsafe {ANSWERS=answers;CALLS=[Call(0,F(0),F(0));64];NEXT=0;}}
fn call(op:u8,a:F,b:F)->F {unsafe {let i=NEXT;assert!(i<64);CALLS[i]=Call(op,a,b);NEXT+=1;F(ANSWERS[i])}}
fn trace()->([Call;64],usize) {unsafe {(CALLS,NEXT)}}
impl F {const ZERO:Self=F(0);fn mul(self,b:Self)->Self {call(2,self,b)}
fn sub(self,b:Self)->Self {call(3,self,b)} fn add(self,b:Self)->Self {call(1,self,b)}
fn mul_m31(self,b:Self)->Self {call(4,self,b)}}
use F as M31;
fn native_factor_step(mut basis:[F;28],mut denominator:F,mut degree:usize,i:usize,j:usize)->([F;28],F,usize) {
                if i == j {
                    return (basis,denominator,degree);
                }
                for k in (0..=degree + 1).rev() {
                    let shifted = if k == 0 { M31::ZERO } else { basis[k - 1] };
                    basis[k] = shifted.sub(basis[k].mul(M31(j as u32)));
                }
                degree += 1;
                denominator = denominator.mul(M31(i as u32).sub(M31(j as u32)));
 (basis,denominator,degree)
}
fn owner_basis_mul(mut basis:[F;28],j:F,mut left:u8)->[F;28] {
 while left!=0 {let k=(left-1) as usize;let shifted=if k==0 {F::ZERO}else{basis[k-1]};
 basis[k]=shifted.sub(basis[k].mul(j));left-=1;} basis
}
fn owner_factor_step(basis:[F;28],den:F,degree:u8,i:u8,j:u8)->([F;28],F,usize) {
 if i==j {(basis,den,degree as usize)} else {
 let basis=owner_basis_mul(basis,F(j as u32),degree+2);
 let den=den.mul(F(i as u32).sub(F(j as u32)));
 (basis,den,(degree+1) as usize)}
}
fn native_acc_step(mut out:[F;28],basis:[F;28],scale:F,k:usize)->[F;28] {
                out[k] = out[k].add(scale.mul_m31(basis[k]));
 out
}
fn owner_acc_step(mut out:[F;28],basis:[F;28],scale:F,k:u8)->[F;28] {
 let index=k as usize;let q=out[index];let m=basis[index];let q1=scale.mul_m31(m);
 let next=q.add(q1);out[index]=next;out
}
#[cfg(kani)] mod proofs {use super::*;
#[kani::proof] #[kani::unwind(66)] fn factor_iteration() {
 let raw:[u32;28]=kani::any();let basis=raw.map(F);let den=F(kani::any());
 let degree:u8=kani::any();let i:u8=kani::any();let j:u8=kani::any();
 kani::assume(degree<=26 && i<28 && j<28);let answers=kani::any();
 reset(answers);let a=native_factor_step(basis,den,degree as usize,i as usize,j as usize);let ta=trace();
 reset(answers);let b=owner_factor_step(basis,den,degree,i,j);let tb=trace();
 assert_eq!(a,b);assert_eq!(ta,tb);
}
#[kani::proof] #[kani::unwind(66)] fn accumulator_iteration() {
 let raw:[u32;28]=kani::any();let out=raw.map(F);let raw:[u32;28]=kani::any();let basis=raw.map(F);
 let scale=F(kani::any());let k:u8=kani::any();kani::assume(k<28);let answers=kani::any();
 reset(answers);let a=native_acc_step(out,basis,scale,k as usize);let ta=trace();
 reset(answers);let b=owner_acc_step(out,basis,scale,k);let tb=trace();
 assert_eq!(a,b);assert_eq!(ta,tb);assert_eq!(ta.1,2);
}
}
}
