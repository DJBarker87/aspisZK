//! Proof-only entrypoints. The imported shipped sources are unchanged.
#[cfg(kani)]
pub fn encoder<E:aspis_core::r0::CodeField>(
    q:&aspis_core::r0::Message<E>, p:aspis_core::r0::domain::Point<E>) -> E {
    aspis_core::r0::encoder::eval_message(q,p)
}
#[cfg(kani)]
pub fn mask(a:&[aspis_core::field::QM31;16], b:&[aspis_core::field::QM31;10],
    g:aspis_core::field::QM31,p:&[aspis_core::field::QM31;10])->aspis_core::field::QM31 {
    aspis_core::state_only_hiding::state_only_selected_mask_value(a,b,g,p)
}
#[cfg(kani)]
pub fn poly(p:&[aspis_core::field::QM31;28],x:aspis_core::field::QM31)->aspis_core::field::QM31 {
    aspis_core::state_only_sumcheck::evaluate_state_only_polynomial(p,x)
}
