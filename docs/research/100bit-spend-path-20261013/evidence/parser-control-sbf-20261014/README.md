# Controlled baseline-source SBF build

This is the single controlled SBF build requested to distinguish source from build-path effects. Before replacing the parser file, the full 751-file candidate source manifest was verified, and candidate `field.rs` was saved. Only `crates/aspis-core/src/field.rs` was restored from the immutable prior P3 source tree. The control manifest has the same 751 paths as the candidate manifest and differs at exactly that file. Both candidate and baseline field bytes are retained here.

The build used the same isolated workspace, `CARGO_TARGET_DIR`, pinned Solana toolchain, features (`pool-adapter,private-leaf-salts`), and release flags as the candidate SBF build; it wrote to `bin-control/`. It completed successfully under 4 GiB high / 6 GiB max / zero swap, with no runtime cost gate run.

All three recorded builds (historical baseline, candidate, control) have 57 stack diagnostics. After normalizing Rust’s 16-hex symbol hash suffixes, the candidate and control diagnostic multisets match all 57 lines. This records diagnostics without assigning them a security or runtime interpretation. Compare the retained full logs and manifest hashes directly.
