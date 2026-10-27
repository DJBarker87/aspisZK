//! Read-only table exporter for the owned reference; outside production Cargo.
fn main() {
    let order = aspis_core::r0::transport::COEFFICIENT_TO_ROW;
    for value in order { println!("{value}"); }
}
