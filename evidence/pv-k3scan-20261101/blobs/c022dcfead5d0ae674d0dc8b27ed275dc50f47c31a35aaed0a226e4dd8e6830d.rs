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
#[cfg(kani)]
pub mod owned;
#[cfg(all(kani,not(pv_cb_extract)))]
mod checks {
    use aspis_core::field::{M31,P};
    #[kani::proof]
    #[kani::unwind(1026)]
    fn encoder_m31() {
        let words:[u32;1024]=kani::any();let mut q=[M31::ZERO;1024];
        for i in 0..1024 {q[i]=M31(words[i]%P);}
        let x:u32=kani::any();let y:u32=kani::any();
        let point=aspis_core::r0::domain::Point{x:M31(x%P),y:M31(y%P)};
        assert_eq!(super::encoder(&q,point),super::owned::encoder(&q,point));
    }
    fn raw_q(words:[u32;4])->aspis_core::field::QM31 {
        use aspis_core::field::{QM31,CM31};
        QM31{c0:CM31{a:M31(words[0]),b:M31(words[1])},c1:CM31{a:M31(words[2]),b:M31(words[3])}}
    }
    #[kani::proof]
    #[kani::unwind(32)]
    fn mask_qm31() {
        use aspis_core::field::QM31;
        let words:[[u32;4];37]=kani::any();
        let mut c1=[QM31::ZERO;16];let mut m=[QM31::ZERO;10];let mut point=[QM31::ZERO;10];
        for i in 0..16 {c1[i]=raw_q(words[i]);}
        for i in 0..10 {m[i]=raw_q(words[16+i]);point[i]=raw_q(words[27+i]);}
        let g=raw_q(words[26]);
        assert_eq!(super::mask(&c1,&m,g,&point),super::owned::mask(c1,m,g,point));
    }
}
