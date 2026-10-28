//! Full native composition candidate; prefix extraction/refinement is pending.
use aspis_core::field::QM31;
use aspis_statement::pool_v1::pair_forest_trace::PoolV1PairForestTraceV1;
use aspis_statement::pool_v1::pair_trace::PoolV1PairTraceErrorV1;

pub fn from_trace(trace: &PoolV1PairForestTraceV1, append_index: u64, lambda: QM31, chi: QM31)
    -> Result<[QM31;1024],PoolV1PairTraceErrorV1> {
    let rows=aspis_prover::host_forest::pool_v1_pair_forest_copy_rows_v1(trace,append_index,lambda)?;
    super::reference224::from_rows(rows,chi).map_err(|_|PoolV1PairTraceErrorV1::CopyImbalance)
}
