//! Concrete source execution diagnostic, never a dependency of shipped code.
extern crate alloc;
pub use aspis_statement::*;
#[path = "../../../../crates/aspis-statement/src/poseidon2.rs"]
mod poseidon2;
#[path = "../../../../crates/aspis-statement/src/spend.rs"]
mod spend;
mod parent;
fn main() { parent::check(); }
