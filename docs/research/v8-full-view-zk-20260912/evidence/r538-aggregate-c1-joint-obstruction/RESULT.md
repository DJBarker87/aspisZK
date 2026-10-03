# Aggregate-C1 initial-claim diagnostic

This is a synthetic R117-based stress diagnostic, not a genuine Fiat–Shamir transcript or a privacy/security proof. It overwrote algebraic z, OOD points, gamma/kappa/tau/alpha after beta had already been sampled; beta is retained from the original run. The selected R28 helper still adds its six ordinary-relation rows to H1, so the result is not an exact current-verifier leaf.

## Frozen sources and pins

The exact local inputs are `performance-current-adapted.rs` (SHA-256 `85a2e77c4b13a41d406e4f068f7a5e7d8db5c9ae3622954e3bbb31cc3735d9e3`) and `r17_c1_witness_audit.rs` (SHA-256 `7fe7d8b0a21f5a568815749ac4d7516472e369e257767526eb23e05dcf301945`). These were copied to the NUC staged candidate and hash-matched before build. Candidate source root: `/home/dombarker/project-offloads/aspis-r117-joint-privacy-stress-20261003-a`; pinned R117 source revision `6677d5f1310ff7373301fbd79f186278f772e68a`. Source SHA list and immutable copies are adjacent.

Build: `cargo build --offline --locked --release --jobs 1 --manifest-path docs/research/v8-no-work-100-20260907/experiments/performance-host/Cargo.toml --bin aspis-v8-performance-host --features insecure-spend-fixture,selected-v7-kernels`, with pinned `rustflags.txt`, in a user systemd scope (`MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`). The changed build passed in 11.22 seconds, max process RSS 550,648 KiB, swap 0. Binary SHA-256 `846a3c15f25cfc579e8db8d976bda7df6a8a74fc4a51bfa597136908ea56c789`; an immutable copy is in `remote/aspis-v8-performance-host`.

An initial build attempt on the earlier helper revision failed with Rust type errors because the generic QM31 `dot` was used on M31 matrices. It was corrected with a local M31 dot and then compiled; original source for the failed attempt is retained in parent history, and the failed service is `run-u777.service` (27.0 seconds, 594,148 KiB RSS, swap 0). No solver ran in that failed build.

## One authorized input and result

The binary itself asserts that its only accepted case is `zero-low22`. Inputs are the accepted OOD parameters `t0=(0,0,1,0)` and `t1=(0,0,2,0)`, gamma=kappa=tau=1, alpha=0, z all-zero, and query indices 0–21. These are synthetic challenge values; beta remains from a different transcript history.

The original per-column C1 observation systems were compatible for all 16 columns. The 4-row total-initial-claim Schur solve was compatible at rank 4 with 2,250 kernel variables. It retained all 1,408 queried raw zeros, 48 point claims, and 32 OOD claims. The exact source `state_only_initial_mask_claim` was equal before/after C1 with mask-only and G fixed, and a separate assertion checked its actual `r17_relation::initial(..., original G)` equals the original `initial` immediately after C1. H1 then passed its unchanged extended 568-row system at rank 544, including its raw/point/OOD/final checks.

The subsequent unchanged 626-row G solve failed: rank 600, one incompatible reduced row (625), with left-kernel support groups `[1,0,1,0,0,0,1]` across semantic/raw/point/final/balance/relation/p2. The run exited 101 after 25.37 seconds, max RSS 250,704 KiB, swap 0. Full run log is `remote/run.log` (SHA-256 `339660f60f6532f21d54318ecbb552c6b12dab8420d49612c0ae035b5736531f`).

The exact G certificate matrix/coefficient file was **not written**: `ASPIS_R117_G_CERT_PATH` was not set on this invocation. The full console summary confirms the certificate was checked internally against all 1,022 columns and had nonzero RHS, but its coefficients cannot be recovered from this log. The old G certificate belongs to the earlier per-column-C1 case and is not a substitute. The total-C1 Schur certificate is correctly absent because its system was compatible. No rerun was made.

This failure concerns this sequential C1/H1/G construction for a synthetic challenge history. It does not establish that the full published-view system has no joint correction, nor does it imply a privacy/security flaw.

## Certificate-only evidence rerun

The lead authorized one exact-input rerun of the immutable binary to recover the missing G certificate. No source or binary changed; only certificate/output paths differed. It reproduced the same C1 Schur and H1 passes and G incompatibility, exiting 101 after 25.59 s at 250,896 KiB RSS and zero swap. The complete matrix/RHS/left-kernel file is `remote/g-left-kernel-rerun.bin` (SHA-256 `cf20fae1ca4c1eaa581ffe11020ba241a9ab800142c8b2c7de73dfab01f42403`). An independent parser checked all 1,022 matrix columns and recomputed nonzero RHS. Exactly three left-kernel coefficients are nonzero: row 256 = `(1,0,0,0)`, row 359 = `(2147483646,0,0,0)` (−1 in M31), and row 625 = `(1,0,0,0)`. The combined RHS is `(2009279124, 375448309, 1725948707, 1391775322)` in the four QM31 limbs, so it is nonzero. The source row classes are semantic row 256, point row 359, and p2 row 625. The parser/check output is `g-certificate-check.json`; its script and SHA-256 are adjacent. Run details are in `remote/run-cert-rerun.log`, with the machine-readable receipt in `certificate-rerun-receipt.json`.
