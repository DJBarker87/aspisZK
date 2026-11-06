use super::*;
#[cfg_attr(not(PCB_NEG_186),kani::ensures(|r| *r==(u64::from(word)<2147483647)))]
#[cfg_attr(PCB_NEG_186,kani::ensures(|r| *r!=(u64::from(word)<2147483647)))]
fn limb(word:u32)->bool {aspis_core::field::M31(word).0<P}
#[kani::proof_for_contract(limb)]fn contract(){let _=limb(kani::any());}
