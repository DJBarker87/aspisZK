//! Concrete source execution diagnostic, never a dependency of shipped code.
extern crate alloc;
pub use aspis_statement::poseidon2;
mod parent;
fn main() { parent::check(); }
