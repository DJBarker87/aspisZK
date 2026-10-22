# Exact Solana SBF Rust std source owner for array construction

This packet closes the old *source unavailable* limitation for the SBF std bodies used by the fixed-array constructor comparison. It identifies the installed `cargo-build-sbf` platform-tools v1.52 Rust source package and verifies two small `core` source files against the exact Anza Rust commit pinned by that package.

The NUC rustc toolchain is `/home/dombarker/.rustup/toolchains/1.89.0-sbpf-solana-v1.52`; `rustc -vV` reports Rust `1.89.0-dev`, LLVM `20.1.7`, and `commit-hash: unknown` / `commit-date: unknown`. The binary SHA-256 is recorded in `toolchain/sbf-metadata.txt`. Separately, the installed platform-tools `version.md` pins its Rust source repository to Anza commit `790f1537507dbdb0da320fbb3b1c1eca3b33c474`. The rust-src tree has no `.git` metadata, so this packet claims a source-package commit, not a recoverable compiler-binary commit.

The installed `core/src/array/mod.rs` hashes to `b5239b8a…7029a1`; `core/src/ops/try_trait.rs` hashes to `bea48e63…96dfa`. Both files were fetched individually from the exact commit's raw GitHub paths (HTTP 200) and the fetched bytes have identical hashes. No toolchain or source archive was downloaded, and no build was run. The raw fetch record is `upstream-fetch.json`.

`compare-critical-bodies.py` verifies those full-file pins and compares seven normalized function bodies among (1) this installed SBF rust-src, (2) the retained Kani 1.93 source snapshot, and (3) the retained upstream Rust 1.89 source snapshot. All seven normalized bodies match:

- `array::from_fn` (SBF lines 102–107), which calls `try_from_fn(NeverShortCircuit::wrap_mut_1(f)).0`;
- `array::try_from_fn` (139–152);
- `try_from_trusted_iterator` (839–859);
- `try_from_fn_erased` (872–898);
- `Guard::push_unchecked` (903–927);
- `NeverShortCircuit::wrap_mut_1`;
- `NeverShortCircuit::branch`.

The exact line spans and normalized body hashes are in `critical-body-comparison.json`. The checker `check_packet.py` reruns only these local source/hash comparisons.

This is source provenance and body-identity evidence. It does not prove that Aeneas translates these methods faithfully, nor establish a Lean operational semantics or an end-to-end source-to-extracted-program refinement. The earlier Kani symbolic result remains a Kani/compiler-level result; this packet narrows the source-version gap but does not turn it into a Lean proof.
