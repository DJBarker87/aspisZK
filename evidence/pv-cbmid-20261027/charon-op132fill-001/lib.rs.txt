//! cfg(kani) extraction context; all source modules are unedited and hash-pinned.
extern crate alloc;
#[cfg(kani)]
pub use aspis_core::field;
#[cfg(kani)]
pub use aspis_statement::*;
#[cfg(kani)]
#[path = "/home/dombarker/project-offloads/codex-pv-cbmid-20261027/source-proof/constraints-fragments.rs"]
pub mod constraints_v4;
#[cfg(kani)]
pub mod pool_v1 {
    pub use aspis_statement::pool_v1::*;
    #[path = "/home/dombarker/project-offloads/codex-pv-cbmid-20261027/source-proof/hiding-with-harness.rs"]
    pub mod hiding;
    #[path = "/home/dombarker/project-offloads/codex-pv-cbmid-20261027/source-proof/oracle-fragments.rs"]
    pub mod oracle;
}
#[cfg(kani)]
pub mod r0 {
    pub use aspis_core::r0::*;
    #[path = "/home/dombarker/project-offloads/codex-pv-cb3-20261026/source/crates/aspis-core/src/r0/encoder.rs"]
    pub mod encoder;
    #[path = "/home/dombarker/project-offloads/codex-pv-cb3-20261026/source/crates/aspis-core/src/r0/basis.rs"]
    pub mod basis;
}
#[cfg(kani)]
pub mod reference;
#[cfg(all(kani,not(pv_cb_extract)))]
mod checks {
    use aspis_statement::pool_v1::pair_forest_hiding::*;
    #[kani::proof]
    #[kani::unwind(1025)]
    fn masks_complete() {
        assert_eq!(pool_v1_pair_forest_copy_active_row_masks_v1(),crate::reference::masks());
    }
    #[kani::proof]
    #[kani::unwind(257)]
    fn rows_complete() {
        assert_eq!(pool_v1_pair_forest_copy_active_rows_v1(),crate::reference::rows());
    }
}

#[cfg(kani)]
pub mod reference_encoder;
#[cfg(all(kani,not(pv_cb_extract)))]
mod schedule_checks {
    #[kani::proof]
    #[kani::unwind(137)]
    fn schedule_success() {
        let result=aspis_statement::pool_v1::pair_forest_hiding::build_pool_v1_pair_forest_copy_row_schedule_v1();
        assert!(matches!(result,Ok(ref links) if links.len()==136));
    }
}
#[cfg(all(kani,not(pv_cb_extract)))]
mod encoder_checks {
    use aspis_core::field::{QM31,CM31,M31,P};
    fn q(r:[u32;4])->QM31 {
        QM31{c0:CM31{a:M31(r[0]),b:M31(r[1])},c1:CM31{a:M31(r[2]),b:M31(r[3])}}
    }
    fn canonical(x:QM31) {
        kani::assume(x.c0.a.0<P);kani::assume(x.c0.b.0<P);
        kani::assume(x.c1.a.0<P);kani::assume(x.c1.b.0<P);
    }
    #[kani::proof]
    #[kani::unwind(1025)]
    fn eval_qm31_complete() {
        let words:[[u32;4];1024]=kani::any();
        let coefficients:[QM31;1024]=core::array::from_fn(|i|q(words[i]));
        for coefficient in coefficients {canonical(coefficient);}
        let xy:[[u32;4];2]=kani::any();
        let point=aspis_core::r0::domain::Point{x:q(xy[0]),y:q(xy[1])};
        canonical(point.x);canonical(point.y);
        assert_eq!(aspis_core::r0::encoder::eval_message(&coefficients,point),crate::reference_encoder::eval_message_indexed(&coefficients,point));
    }
}
#[cfg(kani)]
pub mod reference_multilinear;
#[cfg(all(kani,not(pv_cb_extract)))]
mod multilinear_checks {
    use aspis_core::field::{QM31,CM31,M31,P};
    fn q(r:[u32;4])->QM31 {
        QM31{c0:CM31{a:M31(r[0]),b:M31(r[1])},c1:CM31{a:M31(r[2]),b:M31(r[3])}}
    }
    fn canonical(x:QM31) {
        kani::assume(x.c0.a.0<P);kani::assume(x.c0.b.0<P);
        kani::assume(x.c1.a.0<P);kani::assume(x.c1.b.0<P);
    }
    fn coefficients()->[QM31;1024] {
        let raw:[[u32;4];1024]=kani::any();
        let out=core::array::from_fn(|i|q(raw[i]));
        for x in out {canonical(x);}
        out
    }
    #[kani::proof]
    #[kani::unwind(1025)]
    fn boolean_vertices() {
        let column=coefficients();let bits:[bool;10]=kani::any();
        let point=core::array::from_fn(|i|if bits[i] {QM31::ONE}else{QM31::ZERO});
        assert_eq!(aspis_statement::constraints_v4::multilinear_evaluate_qm31(&column,&point),crate::reference_multilinear::evaluate(&column,&point));
    }
    #[kani::proof]
    #[kani::unwind(1025)]
    fn one_non_boolean_prefix() {
        let column=coefficients();let bits:[bool;9]=kani::any();
        let raw:[u32;4]=kani::any();let first=q(raw);canonical(first);
        kani::assume(first!=QM31::ZERO && first!=QM31::ONE);
        let point=core::array::from_fn(|i|if i==0 {first} else if bits[i-1] {QM31::ONE}else{QM31::ZERO});
        assert_eq!(aspis_statement::constraints_v4::multilinear_evaluate_qm31(&column,&point),crate::reference_multilinear::evaluate(&column,&point));
    }
}
#[cfg(all(kani,not(pv_cb_extract)))]
mod cell_checks {
    #[kani::proof]
    #[kani::unwind(1025)]
    fn cells_complete() {
        assert_eq!(aspis_statement::pool_v1::pair_forest_hiding::pool_v1_pair_forest_relation_free_mask_cells_v1(),crate::reference::cells());
    }
}
