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
fn fixed_accumulator_step<const J:usize>() {
 let rows:[[u64;4];64]=kani::any(); let j=J;let observe:usize=kani::any();
 kani::assume(j<64 && observe<64);
 let power:K=kani::any();let basis:M31=kani::any();let terms:usize=kani::any();
 kani::assume(k_ok(power) && basis.0<P && terms<22 && row_safe(rows[j],power,basis));
 let mut weights=BatchedWeights{raw:rows.to_vec(),terms};
 weights.push(j,power,basis);
 let expected=if observe==j {row_spec(rows[j],power,basis,terms&3==3)} else {rows[observe]};
 assert!(row_equal(weights.raw[observe],expected));
 assert_eq!(weights.raw.len(),64); assert_eq!(weights.terms,terms);
}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_00() {fixed_accumulator_step::<0>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_01() {fixed_accumulator_step::<1>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_02() {fixed_accumulator_step::<2>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_03() {fixed_accumulator_step::<3>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_04() {fixed_accumulator_step::<4>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_05() {fixed_accumulator_step::<5>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_06() {fixed_accumulator_step::<6>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_07() {fixed_accumulator_step::<7>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_08() {fixed_accumulator_step::<8>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_09() {fixed_accumulator_step::<9>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_10() {fixed_accumulator_step::<10>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_11() {fixed_accumulator_step::<11>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_12() {fixed_accumulator_step::<12>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_13() {fixed_accumulator_step::<13>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_14() {fixed_accumulator_step::<14>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_15() {fixed_accumulator_step::<15>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_16() {fixed_accumulator_step::<16>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_17() {fixed_accumulator_step::<17>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_18() {fixed_accumulator_step::<18>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_19() {fixed_accumulator_step::<19>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_20() {fixed_accumulator_step::<20>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_21() {fixed_accumulator_step::<21>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_22() {fixed_accumulator_step::<22>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_23() {fixed_accumulator_step::<23>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_24() {fixed_accumulator_step::<24>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_25() {fixed_accumulator_step::<25>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_26() {fixed_accumulator_step::<26>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_27() {fixed_accumulator_step::<27>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_28() {fixed_accumulator_step::<28>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_29() {fixed_accumulator_step::<29>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_30() {fixed_accumulator_step::<30>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_31() {fixed_accumulator_step::<31>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_32() {fixed_accumulator_step::<32>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_33() {fixed_accumulator_step::<33>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_34() {fixed_accumulator_step::<34>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_35() {fixed_accumulator_step::<35>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_36() {fixed_accumulator_step::<36>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_37() {fixed_accumulator_step::<37>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_38() {fixed_accumulator_step::<38>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_39() {fixed_accumulator_step::<39>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_40() {fixed_accumulator_step::<40>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_41() {fixed_accumulator_step::<41>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_42() {fixed_accumulator_step::<42>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_43() {fixed_accumulator_step::<43>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_44() {fixed_accumulator_step::<44>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_45() {fixed_accumulator_step::<45>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_46() {fixed_accumulator_step::<46>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_47() {fixed_accumulator_step::<47>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_48() {fixed_accumulator_step::<48>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_49() {fixed_accumulator_step::<49>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_50() {fixed_accumulator_step::<50>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_51() {fixed_accumulator_step::<51>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_52() {fixed_accumulator_step::<52>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_53() {fixed_accumulator_step::<53>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_54() {fixed_accumulator_step::<54>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_55() {fixed_accumulator_step::<55>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_56() {fixed_accumulator_step::<56>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_57() {fixed_accumulator_step::<57>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_58() {fixed_accumulator_step::<58>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_59() {fixed_accumulator_step::<59>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_60() {fixed_accumulator_step::<60>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_61() {fixed_accumulator_step::<61>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_62() {fixed_accumulator_step::<62>();}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(row_step)] fn accumulator_slot_63() {fixed_accumulator_step::<63>();}
