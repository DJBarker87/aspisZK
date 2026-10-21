# S4 N8 `wideFromLimbs` ABI bridge

This focused packet proves the canonical eight-limb success behavior for an explicit adapter backed by the accepted EbyKFinish ABI theorem. It does not assert that the generated `FourDotsOps.wideFromLimbs` slot is installed with that adapter: the generic theorem keeps this as an explicit binding premise. Source byte identity between the frozen Rust `wide_exact.rs` and the EbyKFinish extraction input is evidence for a future source/ABI bridge, not a Lean proof of the current generated slot.

The successful target uses Lean 4.32.0 with `-j1 -M 4400`, completed in 12.909s at 2,271,215,616 bytes peak process RSS, 2,252,013,568 bytes sampled aggregate RSS, and zero swap. Its axiom audit is standard-only: `propext`, `Classical.choice`, `Quot.sound`. Attempts v1–v5 are retained under `diagnostics/`; they failed on array extensionality/index proofs and are superseded by v6.
