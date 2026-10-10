//! Native P1 C5 field-shape observation; never part of an SBF verifier.
#[cfg(target_os = "solana")]
compile_error!("P1 narrow preflight is native only");
extern crate std;
use crate::field::WideExact as E;
#[derive(Clone, Debug)]
pub struct Record {
    pub gamma: [u32; 8],
    pub alpha_e: [u32; 8],
    pub alpha_k: [u32; 8],
    pub high_q: usize,
    pub high_f_e: usize,
    pub high_f_k: usize,
    pub first_index: usize,
    pub first_value: [u32; 8],
    pub first_q: [[u32; 8]; 4],
}
std::thread_local! {static RECORD:std::cell::RefCell<Option<Record>>=const{std::cell::RefCell::new(None)};}
pub fn inspect(q: &[E; 1024], gamma: E, alpha_e: E, alpha_k: E) {
    let f_e = super::fold::fold_message(alpha_e, q);
    let f_k = super::fold::fold_message(alpha_k, q);
    let first_index = f_k.iter().position(|x| !x.c1().is_zero()).unwrap_or(0);
    let record = Record {
        gamma: gamma.to_limbs(),
        alpha_e: alpha_e.to_limbs(),
        alpha_k: alpha_k.to_limbs(),
        high_q: q.iter().filter(|x| !x.c1().is_zero()).count(),
        high_f_e: f_e.iter().filter(|x| !x.c1().is_zero()).count(),
        high_f_k: f_k.iter().filter(|x| !x.c1().is_zero()).count(),
        first_index,
        first_value: f_k[first_index].to_limbs(),
        first_q: core::array::from_fn(|s| q[4 * first_index + s].to_limbs()),
    };
    RECORD.with(|r| *r.borrow_mut() = Some(record));
}
pub fn take() -> Record {
    RECORD.with(|r| r.borrow_mut().take().expect("prover preflight observation"))
}
