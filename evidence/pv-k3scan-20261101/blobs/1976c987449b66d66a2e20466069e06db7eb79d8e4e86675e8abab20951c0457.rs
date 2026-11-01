use alloc::vec::Vec;
use aspis_core::field::QM31;
use aspis_statement::logup::build_copy_logup_helper;
use aspis_statement::pool_v1::pair_trace::PoolV1PairTraceErrorV1;
use aspis_statement::pool_v1::pair_forest_trace::{PoolV1PairForestTraceV1,pool_v1_pair_forest_copy_rows_v1};
pub fn build_pool_v1_pair_forest_copy_helper_v1(
    trace: &PoolV1PairForestTraceV1,
    append_index: u64,
    lambda: QM31,
    chi: QM31,
) -> Result<Vec<QM31>, PoolV1PairTraceErrorV1> {
    let rows = pool_v1_pair_forest_copy_rows_v1(trace, append_index, lambda)?;
    build_copy_logup_helper(&rows, chi).map_err(|_| PoolV1PairTraceErrorV1::CopyImbalance)
}
