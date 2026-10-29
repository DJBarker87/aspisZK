#[path="src/tools/r1-cost-probe/src/bin/devnet_spend/diagnostics.rs"]
mod diagnostics;
unsafe extern "C" { fn pv_dispatch_counts() -> u64; }
fn main() {
    diagnostics::initialize();
    if std::env::args().nth(1).as_deref() == Some("oom") {
        std::hint::black_box(Vec::<u8>::with_capacity(usize::MAX / 4));
        unreachable!();
    }
    std::env::set_var("RUST_BACKTRACE", "full");
    std::env::set_var("RUST_LIB_BACKTRACE", "1");
    assert_eq!(std::backtrace::Backtrace::capture().status(), std::backtrace::BacktraceStatus::Disabled);
    let e = anyhow::anyhow!("test error");
    assert_eq!(e.backtrace().status(), std::backtrace::BacktraceStatus::Disabled);
    let mut bytes = [0u8;64];
    let ok = getrandom::fill(&mut bytes).is_ok();
    println!("ok={ok} counts={}", unsafe { pv_dispatch_counts() });
}
