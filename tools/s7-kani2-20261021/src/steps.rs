use super::*;
#[kani::requires(raw<=u64::MAX-u64::from(limb)*u64::from(basis.0))]
#[kani::ensures(|r:&u64| *r==scalar_spec(raw,limb,basis.0,flush))]
fn lane0(raw:u64,limb:u32,basis:M31,flush:bool)->u64 {
 let mut row=[0;4]; let j=0; let old=raw;
 row[j]=old+u64::from(limb)*u64::from(basis.0);
 if flush {let limb=&mut row[j]; *limb=(*limb&0x7fff_ffff)+(*limb>>31);}
 row[j]
}
#[kani::proof_for_contract(lane0)]
#[kani::unwind(6)]
fn lane0_contract() {lane0(kani::any(),kani::any(),kani::any(),kani::any());}
#[kani::requires(raw<=u64::MAX-u64::from(limb)*u64::from(basis.0))]
#[kani::ensures(|r:&u64| *r==scalar_spec(raw,limb,basis.0,flush))]
fn lane1(raw:u64,limb:u32,basis:M31,flush:bool)->u64 {
 let mut row=[0;4]; let j=1; let old=raw;
 row[j]=old+u64::from(limb)*u64::from(basis.0);
 if flush {let limb=&mut row[j]; *limb=(*limb&0x7fff_ffff)+(*limb>>31);}
 row[j]
}
#[kani::proof_for_contract(lane1)]
#[kani::unwind(6)]
fn lane1_contract() {lane1(kani::any(),kani::any(),kani::any(),kani::any());}
#[kani::requires(raw<=u64::MAX-u64::from(limb)*u64::from(basis.0))]
#[kani::ensures(|r:&u64| *r==scalar_spec(raw,limb,basis.0,flush))]
fn lane2(raw:u64,limb:u32,basis:M31,flush:bool)->u64 {
 let mut row=[0;4]; let j=2; let old=raw;
 row[j]=old+u64::from(limb)*u64::from(basis.0);
 if flush {let limb=&mut row[j]; *limb=(*limb&0x7fff_ffff)+(*limb>>31);}
 row[j]
}
#[kani::proof_for_contract(lane2)]
#[kani::unwind(6)]
fn lane2_contract() {lane2(kani::any(),kani::any(),kani::any(),kani::any());}
#[kani::requires(raw<=u64::MAX-u64::from(limb)*u64::from(basis.0))]
#[kani::ensures(|r:&u64| *r==scalar_spec(raw,limb,basis.0,flush))]
fn lane3(raw:u64,limb:u32,basis:M31,flush:bool)->u64 {
 let mut row=[0;4]; let j=3; let old=raw;
 row[j]=old+u64::from(limb)*u64::from(basis.0);
 if flush {let limb=&mut row[j]; *limb=(*limb&0x7fff_ffff)+(*limb>>31);}
 row[j]
}
#[kani::proof_for_contract(lane3)]
#[kani::unwind(6)]
fn lane3_contract() {lane3(kani::any(),kani::any(),kani::any(),kani::any());}
#[kani::requires(k_ok(power) && basis.0<P && row_safe(row,power,basis))]
#[kani::ensures(|r:&[u64;4]| row_equal(*r,row_spec(row,power,basis,flush)))]
fn row_step(row:[u64;4],power:K,basis:M31,flush:bool)->[u64;4] {
let limbs=[power.c0.a.0,power.c0.b.0,power.c1.a.0,power.c1.b.0];
 [lane0(row[0],limbs[0],basis,flush),lane1(row[1],limbs[1],basis,flush),
  lane2(row[2],limbs[2],basis,flush),lane3(row[3],limbs[3],basis,flush)]
}
#[kani::proof_for_contract(row_step)]
#[kani::stub_verified(lane0)] #[kani::stub_verified(lane1)]
#[kani::stub_verified(lane2)] #[kani::stub_verified(lane3)]
#[kani::unwind(6)]
fn row_step_contract(){row_step(kani::any(),kani::any(),kani::any(),kani::any());}
struct BatchedWeights { raw:Vec<[u64;4]>,terms:usize }
fn update_residue_row(row:&mut[u64;4],power:K,basis:M31,flush:bool){*row=row_step(*row,power,basis,flush);}
impl BatchedWeights {
fn push(&mut self,index:usize,power:K,basis:M31) {
let flush=self.terms&3==3;
        update_residue_row(&mut self.raw[index],power,basis,flush);
}
}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)]
fn accumulator_row_step() {
 let rows:[[u64;4];64]=kani::any(); let j:usize=kani::any();let observe:usize=kani::any();
 kani::assume(j<64 && observe<64);
 let power:K=kani::any();let basis:M31=kani::any();let terms:usize=kani::any();
 kani::assume(k_ok(power) && basis.0<P && terms<22 && row_safe(rows[j],power,basis));
 let mut weights=BatchedWeights{raw:rows.to_vec(),terms};
 weights.push(j,power,basis);
 let expected=if observe==j {row_spec(rows[j],power,basis,terms&3==3)} else {rows[observe]};
 assert!(row_equal(weights.raw[observe],expected));
 assert_eq!(weights.raw.len(),64); assert_eq!(weights.terms,terms);
}
