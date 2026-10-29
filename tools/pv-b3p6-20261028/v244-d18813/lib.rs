//! Owned byte-identical deployed host terminal. No reference law is claimed yet.
extern crate alloc;
#[path="../v244/host_terminal_field.rs"] mod host_terminal_field;
#[path="../v244/host_copy_terminal.rs"] mod host_copy_terminal;
#[path="../v244/host_terminal.rs"] pub mod host_terminal;

pub mod reference_terminal;

/// Owned entry with identical argument and complete Result signature.
pub fn reference227(public: reference_terminal::r0::Public<'_>, claims: &[[aspis_core::field::QM31;29];3], alpha: &[aspis_core::field::QM31;10], c: &aspis_core::state_only_prefix::r0::Challenges) -> Result<aspis_core::field::QM31,aspis_core::state_only_prefix::r0::Error> {
    public.terminal_qm31(claims,alpha,c)
}

#[path="../v244/std194227.rs"] pub mod std194227;

mod reference_copy_terminal;

#[path="../v244/reference_field.rs"] mod reference_field;
#[path="../v244/reference_poseidon.rs"] mod reference_poseidon;

fn q13(n:u32)->aspis_core::field::QM31 { use aspis_core::field::{M31,CM31,QM31,P};QM31{c0:CM31::new(M31(n%P),M31(n.wrapping_mul(17)%P)),c1:CM31::new(M31(n.wrapping_mul(31)%P),M31(n.wrapping_mul(47)%P))}}
fn emit13(name:&str,seed:u32,values:&[aspis_core::field::QM31]) {
 let mut words:Vec<u32>=values.iter().flat_map(|x|[x.c0.a.0,x.c0.b.0,x.c1.a.0,x.c1.b.0]).collect();
 if std::env::args().any(|x|x=="--negative")&&name=="add_preweighted"&&seed==0 {words[0]^=1;}
 println!("{{\"function\":\"{name}\",\"seed\":{seed},\"limbs\":{words:?}}}");
}
pub fn d18813(){assert!(!cfg!(debug_assertions));for seed in [0,1,7,19] {reference_terminal::observations13(seed);reference_copy_terminal::observations13(seed);}}
pub fn selector49_fixture13(){reference_terminal::selector49_fixture13();}
