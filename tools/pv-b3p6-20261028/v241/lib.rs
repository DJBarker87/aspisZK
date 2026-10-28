pub mod reference224;
#[test]
fn finite224_rows() {
    use aspis_core::field::{M31,QM31,CM31};
    use aspis_statement::logup::{CopyLogUpRow,build_copy_logup_helper};
    let q=|n|QM31::from_cm31(CM31::from_m31(M31(n)));
    let empty=CopyLogUpRow {producer_values:[q(0);2],producer_weights:[M31::ZERO;2],consumer_values:[q(0);2],consumer_weights:[M31::ZERO;2]};
    let mut checked=0;
    for pattern in 0..16u32 {
        for pole in 0..5usize {
            let mut rows=[empty;1024];
            for r in 0..1024 {
                rows[r].producer_values=[q(1),q(2)];rows[r].consumer_values=[q(3),q(4)];
                rows[r].producer_weights=[M31(pattern&1),M31((pattern>>1)&1)];
                rows[r].consumer_weights=[M31((pattern>>2)&1),M31((pattern>>3)&1)];
            }
            let chi=if pole==0 {q(9)} else {q(pole as u32)};
            let native=build_copy_logup_helper(&rows,chi).map_err(|_|reference224::Error::CopyImbalance);
            let reference=reference224::from_rows(rows,chi).map(|a|a.to_vec());
            assert_eq!(native,reference);checked+=1;
        }
    }
    println!("finite validation: {checked} same-input helper row arrays, every zero-weight pattern and each active pole position");
}
