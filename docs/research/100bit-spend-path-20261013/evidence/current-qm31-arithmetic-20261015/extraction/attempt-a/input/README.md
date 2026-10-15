# QM31 arithmetic extraction input (prepared only)

This isolated, dependency-free Cargo crate copies the current proof-worktree `field.rs` and `field/wide_exact.rs` byte-for-byte and adds only `qm31_add_mul_probe`, a free-function entry point calling `QM31::add` and `QM31::mul`. Cargo default features are empty; `r0-op-count`, `r0-r91-audit`, and `r0-e4-reference` are defined but not enabled. No arithmetic body is copied into the probe.

`source-pins.json` gives exact source paths and SHA-256 values. `tool-pins.json` records the local macOS arm64 Charon/Aeneas executables, versions, and source checkout revisions. `expected-commands.json` records the verified CLI command shape and Rust nightly. Charon help confirms `--start-from` selects an item and reachable call graph; `--include` and `--exclude` controls also exist. The selected free function avoids Charon's unsupported inherent-impl start-path pattern.

This kit has not been compiled or extracted. Charon/Aeneas translation would mechanically expose the copied source call graph only. It would not by itself prove that verifier acceptance or the inline Horner loop in `r1_semantic.rs` corresponds to a Lean predicate. The local binary pins differ from previously recorded NUC tool pins.
