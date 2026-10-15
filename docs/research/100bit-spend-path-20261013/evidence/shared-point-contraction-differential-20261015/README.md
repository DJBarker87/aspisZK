# Shared-point contraction differential

This focused native test compares the pinned baseline and isolated candidate `Weights::pair` implementations. The test compiles the actual saved `weights.baseline.rs` and `weights.candidate.rs` source files. It does not change the live implementation.

The release test passed on the pinned NUC workspace: exit 0, 1 test passed, 0 failed. The test asserts equality of the complete `Result` on 72 comparisons. Its S2 cases include seeded `Weights::new` constructions with zero, unit, boundary (`P−1`), and random canonical challenges, points, fold challenges, coefficients, and kappa values. It also covers manual low-factor equality cases (all zero, all two, and seeded random nonzero factors), with distinct `d0`/`d1` scales on the latter; a one-cell mismatch exercises the fallback guard. S1/D output and malformed-length error parity are included as controls.

The original manual case used different `d0`/`d1` factor arrays but did **not** produce distinct nonzero combined scales: one factor in each product was zero. The earlier output and source are retained unchanged. The corrected case explicitly asserts scales `1/16` and `6/16`, both nonzero and unequal; see the later [scale-fix differential evidence](../shared-point-contraction-differential-scale-fix-20261015/README.md).

The run used `cargo test --release --locked --offline -p aspis-r1-cost-probe --test shared_point_contraction_equivalence`, with `CARGO_BUILD_JOBS=2` and the existing pinned v1.52 target cache. Wall time was 28.64 seconds, mostly compilation; the test itself took 0.01 seconds. Peak RSS was 539,528 KiB and swap use was zero. The command ran under `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`, and `TasksMax=128`.

The source workspace was based on `aba310f1daa065a27da89d15c6c47166037a8a71`; its prepared candidate manifest records 751 source paths, with only the package's `weights.rs` replaced by the isolated candidate. Separate `inputs/` files pin the baseline/candidate implementation files and this differential test. Rust was 1.94.1 and Cargo was 1.94.1 on x86_64 Linux. The exact compiler output, timing report, and status are preserved in `remote/`.

This finite differential is implementation evidence for the tested inputs. It is not a proof of equivalence for all values, a benchmark, a source-level theorem, or a protocol/security result. The candidate remains isolated; no runtime source was adopted by this task.
