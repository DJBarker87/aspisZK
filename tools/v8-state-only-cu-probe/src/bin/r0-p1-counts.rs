#[cfg(not(feature = "r0-op-count"))]
fn main() {
    panic!("enable r0-op-count");
}
#[cfg(feature = "r0-op-count")]
fn main() {
    use aspis_core::r0_op_count as counts;
    use aspis_statement::r0_probe::Phase;
    use std::{cell::RefCell, path::PathBuf};
    std::thread_local! {static PHASES: RefCell<Vec<serde_json::Value>> = const {RefCell::new(Vec::new())};}
    fn trace(p: Phase) {
        let (inclusive, exclusive) = counts::take();
        let map = |values: [u64; counts::N]| {
            counts::NAMES
                .iter()
                .zip(values)
                .map(|(k, v)| ((*k).to_owned(), serde_json::json!(v)))
                .collect::<serde_json::Map<_, _>>()
        };
        PHASES.with(|p2|p2.borrow_mut().push(serde_json::json!({"phase":format!("{p:?}"),"inclusive":map(inclusive),"exclusive":map(exclusive)})));
    }
    fn hash(parts: &[&[u8]]) -> [u8; 32] {
        counts::hash(parts);
        aspis_prover::HOST_HASH(parts)
    }
    let args: Vec<_> = std::env::args().collect();
    let dir = PathBuf::from(&args[1]);
    let variant = &args[2];
    let bytes = std::fs::read(dir.join(format!("{variant}.proof.bin"))).unwrap();
    let public = std::fs::read(dir.join(format!("{variant}.public.bin"))).unwrap();
    let public =
        aspis_statement::pool_v1::decode_pool_v1_pair_forest_terminal_statement_v1(&public)
            .unwrap();
    counts::take();
    aspis_statement::r0_probe::r0_verify(
        aspis_prover::r0_fixture::statement_public(&public),
        &bytes,
        hash,
        Some(trace),
    )
    .unwrap();
    let result = serde_json::json!({"variant":variant,"source_revision":std::env::var("ASPIS_SOURCE_REVISION").unwrap(),
        "accepted":true,"nested_counts":"inclusive for audit; exclusive excludes primitives nested inside another priced primitive",
        "phases":PHASES.with(|p|p.borrow().clone())});
    std::fs::write(&args[3], serde_json::to_vec_pretty(&result).unwrap()).unwrap();
}
