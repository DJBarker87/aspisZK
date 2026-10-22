extern crate alloc;
pub mod sim {
    // Compile the very same source file, with no copied implementation or stub.
    #[path="/home/dombarker/project-offloads/codex-cx-prover-commit32-20261022/src/crates/aspis-r1-cost-probe/src/sim_owned32.rs"]
    pub mod owned32;
    include!("/home/dombarker/project-offloads/codex-cx-prover-commit32-20261022/harness/publication-kani32-bounded.rs");
}
