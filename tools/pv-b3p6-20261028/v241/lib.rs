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
#[cfg(any(test,feature="full-root"))]
pub mod full_reference224;

#[test]
fn finite224_full_prefix() {
    use aspis_core::field::{M31,CM31,QM31};
    let q=|n|QM31::from_cm31(CM31::from_m31(M31(n)));
    let mut checks=0;
    for withdrawal in [false,true] {
        let fixture=aspis_prover::r0_fixture::prepare(withdrawal);
        let trace=&fixture.compiled.trace;
        for index in [0,1,(1<<20)-1,u64::MAX] {
            for lambda in [q(0),q(17)] {
                for chi in [q(0),q(23)] {
                    let original=aspis_statement::pool_v1::pair_forest_semantic_oracle::build_pool_v1_pair_forest_copy_helper_v1(trace,index,lambda,chi);
                    let host=aspis_prover::host_forest::materialize_copy_helper(trace,index,lambda,chi);
                    let reference=full_reference224::from_trace(trace,index,lambda,chi).map(|a|a.to_vec());
                    assert_eq!(original,host);assert_eq!(host,reference);checks+=1;
                }
            }
        }
    }
    println!("finite validation: {checks} complete same-input original/host/reference trace helper Results; both fixtures, append extremes, lambda0 and pole candidates");
}
pub mod prefix224;
#[cfg(test)]
fn project224(trace:&aspis_statement::pool_v1::pair_forest_trace::PoolV1PairForestTraceV1) -> prefix224::View {
    use aspis_statement::pool_v1::pair_trace::PoolV1PairTraceVariantV1;
    prefix224::View {
        stable:core::array::from_fn(|c|core::array::from_fn(|r|trace.stable.c1[c].get(r).copied())),
        late:core::array::from_fn(|c|core::array::from_fn(|r|trace.late[c].get(r).copied())),
        withdrawal:trace.variant==PoolV1PairTraceVariantV1::Withdrawal,
    }
}
#[test]
fn finite224_owned_prefix() {
    use aspis_core::field::{M31,CM31,QM31};
    let q=|n|QM31::from_cm31(CM31::from_m31(M31(n)));
    let registry=aspis_prover::host_forest::build_pool_v1_pair_forest_copy_registry_v1().unwrap();
    assert_eq!(registry.len,136);
    let mut checks=0;
    for withdrawal in [false,true] {
        let fixture=aspis_prover::r0_fixture::prepare(withdrawal);
        let trace=&fixture.compiled.trace;
        let view=project224(trace);
        for index in [0,1,(1<<20)-1,u64::MAX] {
            for lambda in [q(0),q(17)] {
                let native=aspis_prover::host_forest::pool_v1_pair_forest_copy_rows_v1(trace,index,lambda);
                let reference=prefix224::copy_rows(view,registry.data,index,lambda);
                assert_eq!(native,reference);checks+=1;
            }
        }
    }
    println!("finite validation: {checks} complete owned-prefix row arrays / native; same registry, both projected fixtures, append extremes and lambda0");
}
#[test]
fn fidelity224_prefix_side() {
    use aspis_core::field::{M31,QM31};
    use aspis_statement::logup::CopyLogUpRow;
    use aspis_statement::pool_v1::pair_trace::{PoolV1PairCopyTupleV1,PoolV1PairTupleLimbV1};
    let row=CopyLogUpRow{producer_values:[QM31::ZERO;2],producer_weights:[M31::ZERO;2],consumer_values:[QM31::ZERO;2],consumer_weights:[M31::ZERO;2]};
    let mut rows=[row;1024];
    let view=prefix224::View{stable:[[None;1024];16],late:[[None;1024];16],withdrawal:false};
    let tuple=PoolV1PairCopyTupleV1{row:1023,limbs:[PoolV1PairTupleLimbV1::Zero;16]};
    let words=|r:CopyLogUpRow| {
        let mut xs=Vec::new();
        for v in r.producer_values.into_iter().chain(r.consumer_values) {
            xs.extend([v.c0.a.0,v.c0.b.0,v.c1.a.0,v.c1.b.0]);
        }
        xs.extend(r.producer_weights.map(|w|w.0));xs.extend(r.consumer_weights.map(|w|w.0));xs
    };
    let mut cases=Vec::new();
    for (tag,weight,consumer) in [(7,1,false),(11,0,false),(13,0,false),(17,1,true)] {
        rows=prefix224::side(rows,view,tuple,M31(tag),M31(weight),QM31::ZERO,consumer).unwrap();
        cases.push(words(rows[1023]));
    }
    println!("D188-prefix224-cases={cases:?}");
}
#[test]
fn fidelity224_helper_write() {
    use aspis_core::field::{M31,CM31,QM31};
    use aspis_statement::logup::CopyLogUpRow;
    let q=|n|QM31::from_cm31(CM31::from_m31(M31(n)));
    let empty=CopyLogUpRow{producer_values:[q(0);2],producer_weights:[M31::ZERO;2],consumer_values:[q(0);2],consumer_weights:[M31::ZERO;2]};
    let mut rows=[empty;1024];rows[1023].producer_values[0]=q(1);rows[1023].producer_weights[0]=M31::ONE;
    let out=reference224::from_rows(rows,q(3)).unwrap();
    let words=out.map(|v|[v.c0.a.0,v.c0.b.0,v.c1.a.0,v.c1.b.0]);
    println!("D188-helper224-values={words:?}");
}
