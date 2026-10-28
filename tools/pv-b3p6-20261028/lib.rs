pub mod reference133;
#[cfg(kani)]
mod proofs {
    #[kani::proof]
    #[kani::unwind(32)]
    fn shipped_equals_reference133_pointwise() {
        let shipped = aspis_statement::pool_v1::pair_forest_hiding::pool_v1_pair_forest_copy_active_rows_v1();
        let expected = super::reference133::active_rows();
        match shipped {
            Ok(rows) => { assert_eq!(rows.len(), 214); let index: u8 = kani::any(); kani::assume(index < 214); let i = usize::from(index); assert_eq!(rows[i], expected[i]); }
            Err(_) => assert!(false, "reference success disagrees with shipped error"),
        }
    }
}
#[test]
fn finite_native133() {
 let actual=aspis_statement::pool_v1::pair_forest_hiding::pool_v1_pair_forest_copy_active_rows_v1().unwrap();
 assert_eq!(actual.as_slice(), reference133::active_rows().as_slice());
}

pub mod reference226;
#[cfg(any(kani, test))]
mod native226;
