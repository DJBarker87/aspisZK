# Coupled H1/p2 stress diagnostic

This is one R117-based synthetic stress diagnostic, not a complete privacy proof or a genuine Fiat–Shamir transcript. It overwrites algebraic z, OOD points, gamma/kappa/tau/alpha after beta was sampled; beta is retained from another transcript history, so `fs_history_consistent=false`. The helper also retains the R28 extension of H1 with six ordinary-relation rows; this is not an exact current-verifier leaf.

## Source binding

The staged source revision is `6677d5f1310ff7373301fbd79f186278f772e68a`. Source snapshots are stored by SHA-256 beneath `sources/<sha>/<filename>` and the remote staged files matched before compile. The exact source map is `r17_h1_semantic_audit.rs`, SHA-256 `f16df7cda242734d0de3b64bdec1a1972123d763183211c2aedf22fa054141b6`; the pinned `payment_extraction.rs` (SHA `957060c7556d2a0365c1cb3d2bf0576a72399c6c20bfbb47ea531f110dba54f5`) includes it. The map returns 271 source coordinates over 1024 positions. The other changed inputs are `performance-current-adapted.rs` SHA `0b69aa4ebb330a291cee674c4e4244eb214ea2b0add3c1353b41c36f398b7f22` and `r17_c1_witness_audit.rs` SHA `639ca0c362bc41994b7ecdb8825e5914e5330e1e66b0a012d2a6998f6ff5b530`.

The current R117 source checksums for the unchanged relation/field/basis/circle inputs are in `../current-source/source-sha256.txt`; `r17_host_relation.rs` matches pin `3b7a5040509e0c3ad5e421e49a4f6d1d106c5adabfc2bf891bf8685c66b4b801`. No verifier or Rust product source was changed.

## Build

The focused optimized command and exact environment are preserved in `build.sh`, `metadata/rustflags.txt`, the fingerprint JSON, and the verbose `build-verified.log`. It set `CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS=true`; the verbose Cargo/rustc output contains `-C overflow-checks=on`. Rust is `1.94.1 (e408947bfd200af42db322daf0fadfe7e26d3bd1)`. The build ran as `run-u782.service` with `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`. It exited 0 in 35.37 seconds, max process RSS 594,712 KiB, swap 0. The copied immutable executable SHA-256 is `96860a34d439b0c3c2d1b934f7ae1070397d5bc88a81e37634a1bcd6dfca20f4`.

A prior build invocation, `run-u781.service`, stopped before Cargo because the systemd PATH omitted `/home/dombarker/.cargo/bin`; it exited 127 in 4 ms with 3,520 KiB max RSS and zero swap. Its log is retained separately. The earlier aggregate helper build `run-u777.service` failed with Rust E0308 M31/QM31 dot-product type mismatches in `r17_c1_witness_audit.rs` (including lines 348, 377, 393 and 486). The helper source at that attempt was `.r21-scratch/r117-joint-privacy-stress/r17_c1_witness_audit.rs`, SHA-256 `699a038898ed9bd4528a9861549b2d6f861e05da142aa49c5af246bfad5743dd`. That path was overwritten by the corrected helper and no immutable copy of the earlier bytes or full stderr log remains. This missing artifact is recorded rather than reconstructed. The failure occurred before any solver execution. The corrected helper source is retained by SHA above.

## One authorized case

The executable asserts that it accepts only `zero-low22`: source-accepted OOD parameters `t0=(0,0,1,0)` and `t1=(0,0,2,0)`, gamma=kappa=tau=1, alpha=0, z all zero, and query indices 0 through 21. No other stress case ran.

The total-C1 initial-claim Schur solve remained compatible at rank 4 with 2,250 kernel variables. All 16 original C1 108-row systems passed, including 1,408 raw zeros, 48 point claims and 32 OOD claims. The exact source `state_only_initial_mask_claim` was preserved with mask-only and G held fixed, and the independent actual `r17_relation::initial(..., original G)` assertion passed immediately after C1.

The unmodified H1 solve remained 568 equations and passed at rank 544 with 24 compatibility residual rows. The code then evaluated the exact source `r17_h1_semantic_audit` map on C1-corrected messages, used row 256 and the first H1 pad to append one coupled equation to H1, and solved the 569-row system at rank 545 with 24 compatibility residuals. All 568 original H1 equations and source checks remained enforced. The map-predicted row-256 change matched a fresh full semantic-delta computation; independently, `dot(dw, returned_total) == gamma^27 * semantic_delta[256]` passed.

The unchanged 626-row G solve was compatible at rank 600. Its original p0 and p2 targets, all seven relation coefficients, all 271 semantic cancellations, 88 raw zeros, 3 point claims, 2 OOD claims and 256 final values passed. The actual C1/H1/G encoders passed, and the complete same-public semantic difference after G was zero. The run exited 0 in 56.81 seconds, max RSS 264,188 KiB, swap 0, as `run-u783.service`. Full output is `run.log` (SHA-256 `85129b13a44273fc4fecea2dad73211e559ada6a6dfde4b021b91b37cabb36f7`); exact command/environment is in `run.sh`.

C1, H1, and G certificate files were not emitted because all three systems were compatible. This single synthetic history does not establish universal privacy, transcript coupling, probability losses, soundness, or end-to-end security.
