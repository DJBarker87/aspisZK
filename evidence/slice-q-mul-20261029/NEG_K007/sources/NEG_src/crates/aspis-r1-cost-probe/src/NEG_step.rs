use super::*;
const MAX_PRODUCT:u64=4611686009837453316;
const MAX_ROW:u64=13835058046692229131;
#[derive(Clone,Copy)] struct Log{lhs:u32,rhs:u32,value:u64,count:usize}
static mut LOG:Log=Log{lhs:0,rhs:0,value:0,count:0};
fn product(a:u32,b:u32)->u64{
 assert!(a<2147483647 && b<2147483647);
 let p:u64=kani::any();kani::assume(p<=MAX_PRODUCT);
 unsafe{LOG=Log{lhs:a,rhs:b,value:p,count:LOG.count+1};}p
}
// Frozen verifier.rs:237-240, one arbitrary iteration, replacing only the
// product expression by its over-approximation. This is a method experiment,
// NOT execution of the unchanged full native function.
fn row_step(row:&mut[u64;4],limbs:&[u32;4],basis:M31,j:usize){
 let old=residue_limb_at(row,j);let limb=power_limb_at(limbs,j);
 row[j]=old+product(limb,basis.0);
}
#[kani::proof] #[kani::unwind(8)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEG_copy::KMX_copy_nonoverlapping)]
fn row_step_check(){
 let old:[u64;4]=kani::any();let limbs:[u32;4]=kani::any();let basis:u32=kani::any();let j:usize=kani::any();
 kani::assume(j<4 && old[j]<=MAX_ROW && limbs[j]<2147483647 && basis<2147483647);
 unsafe{LOG.count=0;}let mut row=old;row_step(&mut row,&limbs,M31(basis),j);
 unsafe{
 assert!(LOG.count==1 && LOG.lhs==limbs[j] && LOG.rhs==basis);
 let correct=row[j]==old[j]+LOG.value;
 assert!(if cfg!(NEG_wrong_step){!correct}else{correct});
 let k:usize=kani::any();kani::assume(k<4 && k!=j);assert!(row[k]==old[k]);
 }
}
#[kani::proof] #[kani::unwind(8)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEG_copy::KMX_copy_nonoverlapping)]
fn flush_step_check(){
 let old:[u64;4]=kani::any();let j:usize=kani::any();kani::assume(j<4);
 let mut row=old;
 let mut iter=row[j..].iter_mut();let limb=iter.next().unwrap();
 *limb=(*limb&0x7fff_ffff)+(*limb>>31);
 let correct=row[j]==(old[j]&0x7fff_ffff)+(old[j]>>31);
 assert!(if cfg!(NEG_wrong_step){!correct}else{correct});
 let k:usize=kani::any();kani::assume(k<4 && k!=j);assert!(row[k]==old[k]);
}
#[kani::proof] #[kani::unwind(8)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEG_copy::KMX_copy_nonoverlapping)]
fn copy_check(){let x:[u64;4]=kani::any();let y=x;let j:usize=kani::any();kani::assume(j<4);let correct=x[j]==y[j];assert!(if cfg!(NEG_wrong_copy){!correct}else{correct});}
