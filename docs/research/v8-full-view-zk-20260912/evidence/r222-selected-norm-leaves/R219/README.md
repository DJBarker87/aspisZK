# R219 focused circle norm leaf extraction

R219 extracted a small LLBC source closure for the selected `circle_norm::norm` and `circle_norm::polar` roots, with `circle_norm::times_r` and `aspis_core::field` included. Charon ran without `--monomorphize` and without the freeze/standard-library selectors. It used the cached optimized release workspace, the R207 release features, and the exact R207 rustflags.

Before extraction the runner asserted these frozen input hashes: `circle_norm.rs` `3f0882366674d5d41e365e62787d85b62076e6077697e9f756e135ce12aedbd2`, `crates/aspis-core/src/field.rs` `639b6425fe672e0fa6019b99b702d1f08f56cd75c4d9ad6defef854b7640f499`, performance-host `Cargo.toml` `62f81cd54314ec1a637c61404bd6cf6f12f8defbf1ab68fb0ded4956df80646c`, and `Cargo.lock` `a2e3d525c3a0f01428b56df55001ba304981a6b8c26cca08badf7b09b7029814`. Rustflags SHA256: `f2485133cd857d119d387fcdda1a7fe2607e04dbec4756adbaacd3e765363613`. The frozen snapshot had no `.git` directory; the prior recorded source revision is retained as provenance, not independently asserted from this snapshot.

Charon exited 0 and wrote `R219NormLeaves.llbc` (SHA256 `45749d7c4405024c7d06bd4a34ab07ce0f627290e51c98069d6c88af9115e9bb`). The release extraction took 13.81 s, peak RSS 612,680 KiB, swaps 0. The systemd unit used `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, and `TasksMax=128`. The result contains 3 type declarations, 21 function slots, 2 globals, 1 trait, and 1 trait implementation. Function IDs 0, 1, and 3 are `norm`, `polar`, and `times_r`; the LLBC declaration inventory is summarized in `llbc-summary.json`.

This bundle records extraction and source/declaration metadata only. It does not translate the LLBC to Lean, compile a theorem, or make a source-semantics claim.
