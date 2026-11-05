#[cfg(kani)]
mod NJA_contracts {
 use super::*;
 pub const fn NJA_bits_ref(a:Arity)->u32{match a{Arity::Two=>1,Arity::Eight=>3}}
 pub const fn NJA_width_ref(a:Arity)->usize{match a{Arity::Two=>2,Arity::Eight=>8}}
 pub const fn NJA_levels_ref(a:Arity)->u32{match a{Arity::Two=>18,Arity::Eight=>6}}
 #[kani::proof_for_contract(Arity::bits)]
 fn NJA_bits_contract(){let eight:bool=kani::any();let a=if eight{Arity::Eight}else{Arity::Two};let _=a.bits();}
 #[kani::proof_for_contract(Arity::width)]
 fn NJA_width_contract(){let eight:bool=kani::any();let a=if eight{Arity::Eight}else{Arity::Two};let _=a.width();}
 #[kani::proof_for_contract(Arity::levels)]
 fn NJA_levels_contract(){let eight:bool=kani::any();let a=if eight{Arity::Eight}else{Arity::Two};let _=a.levels();}
}
