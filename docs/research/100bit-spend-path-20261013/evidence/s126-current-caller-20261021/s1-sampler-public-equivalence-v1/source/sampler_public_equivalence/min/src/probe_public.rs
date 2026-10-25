#![no_std]
extern crate alloc;
#[path="equality_actual.rs"]pub mod actual;
#[path="equality_reference.rs"]pub mod reference;
#[cfg(kani)] mod value_proofs {
fn same(a:aspis_core::field::WideExact,b:aspis_core::field::WideExact){let a=a.to_limbs();let b=b.to_limbs();let mut j=0;while j<8{assert!(a[j]==b[j]);j+=1;}}
#[kani::proof] #[kani::unwind(10)] fn ordinary_value_equal(){let block=kani::any::<[u8;32]>();same(crate::actual::ordinary_sample(&block),crate::reference::ordinary_sample(&block));kani::cover!(true,"both ordinary samplers return");}
#[kani::proof] #[kani::unwind(10)] fn gamma_value_equal(){let block=kani::any::<[u8;32]>();same(crate::actual::gamma_sample(&block),crate::reference::gamma_sample(&block));kani::cover!(true,"both gamma samplers return");}
}
