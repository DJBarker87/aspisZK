//! cfg(kani) extraction context; all source modules are unedited and hash-pinned.
extern crate alloc;
#[cfg(kani)]
pub use aspis_core::field;
#[cfg(kani)]
pub use aspis_statement::trace_v4;
#[cfg(kani)]
pub mod pool_v1 {
    pub use aspis_statement::pool_v1::*;
    #[path = "/home/dombarker/project-offloads/codex-pv-cb3-20261026/source/crates/aspis-statement/src/pool_v1/pair_forest_hiding.rs"]
    pub mod hiding;
}
#[cfg(kani)]
pub mod r0 {
    pub use aspis_core::r0::*;
    #[path = "/home/dombarker/project-offloads/codex-pv-cb3-20261026/source/crates/aspis-core/src/r0/encoder.rs"]
    pub mod encoder;
    #[path = "/home/dombarker/project-offloads/codex-pv-cb3-20261026/source/crates/aspis-core/src/r0/basis.rs"]
    pub mod basis;
}
