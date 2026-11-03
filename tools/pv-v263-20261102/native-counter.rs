extern crate alloc;
#[path = "../../evidence/pv-v263-20261102/inputs/crates/aspis-r1-cost-probe/src/host_work.rs"]
mod host_work;
fn main() {
    // Keep the generic source and closure in emitted MIR. No source edits or
    // annotations constrain the type of host_work's completed counter.
    let output = host_work::map(200, 27, |i| i);
    assert_eq!(output.len(), 27);
}
