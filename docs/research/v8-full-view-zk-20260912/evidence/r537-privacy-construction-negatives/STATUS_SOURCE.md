# Targeted joint privacy stress diagnostic

This is an R117-source-based diagnostic, not a proof of privacy or a genuine Fiat–Shamir transcript. The case overwrites the algebraic `z`, OOD points, and `gamma/kappa/tau/alpha` after the honest prover has sampled `beta`; the printed beta is retained from the original run, so the challenge history is inconsistent by design.

## Source boundary

The NUC source tree was `/home/dombarker/project-offloads/aspis-r20-r117-primal-20260930-a`, staged into `/home/dombarker/project-offloads/aspis-r117-joint-privacy-stress-20261003-a`. The source manifest reports base/source revision `6677d5f1310ff7373301fbd79f186278f772e68a`.

The staged selected relation source matches the pinned R508 `r17_host_relation.rs` SHA `3b7a5040509e0c3ad5e421e49a4f6d1d106c5adabfc2bf891bf8685c66b4b801`. `circle.rs` and `circle_fri.rs` match R28 pins `8f6f0f32c8dd93e3ee459df0c1d0ef710b01996d3bc929dbeffb3f7d14a0227c` and `77625499c80b30fe9de1e79daaf35dc964bf0cb675a65ced69592d3d421c856b`. `field.rs` (`639b6425fe672e0fa6019b99b702d1f08f56cd75c4d9ad6defef854b7640f499`) and `r16_basis_transport.rs` (`678c64e08e7d14bb6bc160042f0ee01cb39e260748ec1ac95cce008969d586ae`) differ from the R28 archived pins.

The current NUC `r17_c1_witness_audit.rs` is SHA `1aa5c416fd971bb65bf5fd7aab20046a6e13c171dbaf272674337682f57f1a13`. The diagnostic helper extends its H1 system with six ordinary-relation coefficient rows `[0,1,2,3,5,6]`, changing H1 from 562 to 568 equations, and replaces fixed C1/H1 rank gates with augmented-target compatibility checks. These are R28 helper extensions. The G helper remains the original 626-row path, including p0/p2 and all seven relation coefficients. Consequently, results below are not an exact current-verifier leaf.

Diagnostic inputs were accepted OOD parameters `t0=(0,0,1,0)` and `t1=(0,0,2,0)`, `gamma=kappa=tau=1`, `alpha=0`, `z=0`, and queries 0 through 21. The opposite-witness pair is the harness's actual same-public pair; C1 encoding and extraction checks ran.

## Build and run

The release host build used the pinned source flags, `--offline --locked --release --jobs 1`, in a user systemd scope with `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, and `TasksMax=128`. The certificate-instrumented focused build succeeded in 11.74 seconds at 541,224 KiB process RSS, with zero swap. Its executable SHA was `ccdad21e49676d76a925542432aeccd292ac48618d106857ebda80b5c9c11685`; compiled inputs were `performance.rs` SHA `e16d9faf45e40ad238a06ce79454217ba0eeddeb1e4741e192910850c30a65a9` and `r17_c1_witness_audit.rs` SHA `c846cbdbc280adec7aedd11e1187ec3cedb3ec83920d4b7aefa3bea815fbe555`.

The first attempted invocation used an existing output path and stopped before the prover. The next invocation omitted `ASPIS_R17_C1_WITNESS_AUDIT=1`, so it completed the ordinary honest path but did not enter the stress branch. The actual stress invocation set both required audit variables and exited 101 after 24.45 seconds, at 250,368 KiB process RSS and zero swap. The single authorized row-ledger rerun exited 101 after 25.96 seconds at 250,240 KiB RSS and zero swap while writing the certificate.

The stress trace showed:

- C1 affine compatibility succeeded for all 16 columns; it checked 1,408 queried raw zeros, 48 point claims, and 32 OOD claims.
- The extended R28 H1 system succeeded with rank 544 and 568 equations; it checked 88 raw, 3 point, 2 OOD, and all 256 remaining final constraints.
- The following 626-row G augmented target had rank 600 and two nonzero residual rows. The first residual’s left-kernel certificate has only two nonzero coefficients: `row 0 = -1` (semantic constraint 0) and `row 361 = +1` (point constraint 2); the other 624 coefficients are zero. The instrumented run checked this combination on all 1,022 original matrix columns and confirmed a nonzero original RHS before preserving the panic. The original RHS rows are row 0 `(p−1, 0, 596693270, 0)` and row 361 `(0, 0, 0, 0)`, where `p=2147483647`, giving certificate RHS `(1, 0, 1550790377, 0)`.

This failure shows that this sequential C1/H1/G construction did not produce a full correction for this stress input. It does not establish that the complete published-view constraints have no joint correction: the extended H1 step imposes ordinary-relation and per-channel final constraints before G, which can constrain the later G target more strongly than the published combined equations. No rank assumption was used for the diagnostic C1/H1/G solve, and no privacy-bug or security-loss conclusion follows from this synthetic prefix.

The complete original matrix, all 626 RHS values, and all 626 left-kernel coefficients are saved as `evidence/g-left-kernel.bin` (SHA-256 `c3584854f3fb1d7ee31ce34911461f87a4b96212818f158805df03d7b5088a29`); the gzip copy is `evidence/g-left-kernel.bin.gz` (SHA-256 `0e8f74b9d70f31c29b55808ea0ce3b6056c8da6ba6d73bae6f926f783c87de72`). The layout is documented in `evidence/MATRIX_FORMAT.md`. No second input case has been run.


## Initial-mask-preserving C1 follow-up

A lead-directed second diagnostic changed only the C1 correction system: it appended four M31 equations per C1 column, using the actual `state_only_selected_mask_value` at each Boolean point with the source point-bit order. Each legal variable uses the same transport correction as before (`e_r−e_1023` for inactive rows and the existing unit direction for active rows). It sets each column's initial-mask contribution to zero and independently compares the actual source `state_only_initial_mask_claim` before and after C1 correction with mask-only and G values held fixed. H1 and G stayed unchanged, but were not reached.

The first case again used `z=0`, alpha=0, gamma=kappa=tau=1, and queries 0–21, with beta retained from the unrelated original transcript. The 112-equation, 221-variable C1 system for column 0 had rank 96 and one incompatible residual; the left-kernel certificate is exactly coefficient 1 on added row 108. Its matrix row is all zero and its RHS is `p−1`. The saved original matrix/RHS/certificate are in `evidence/c1-left-kernel-col0.bin` (SHA-256 `257466c01d647002e6b6f08cc77e4ff136a7a36d68dd18335f1a4e0a543fc4fa`); gzip SHA-256 `e64d6e52affa83d9e939d5b15a8b770a4b4b3c387973d3b517b7903f349f0201`. See `evidence/C1_MATRIX_FORMAT.md`.

This proves incompatibility only for the selected per-column correction support and the stronger per-column zero target in this synthetic case. It does not rule out a correction where initial-mask contributions cancel across columns, or any other full joint solution.

The changed optimized build exited 0 in 11.05 seconds (546,284 KiB RSS, zero swap) and produced binary SHA `04803d773c16e2b4f2313e56db97de17f83bb877064f312f97eab4c32498aa51`. The one run exited 101 after 6.44 seconds (193,180 KiB RSS, zero swap). Its source files were `performance.rs` SHA `d6cb96979a96517280089dbde62b01353c6e6092f36140f9f142f7374ef18f9f` and `r17_c1_witness_audit.rs` SHA `2635d2ac9573d0d5f22c5b1216810eea84f7a636450207b26e9aea2827d2c3c5`.

## Evidence files

`evidence/` contains the exact initial build failures, successful release build, stress failure logs, and matrix certificate. The source copies are in this directory. The corresponding NUC candidate tree and remaining build logs are under `/home/dombarker/project-offloads/aspis-r117-joint-privacy-stress-20261003-a`.
