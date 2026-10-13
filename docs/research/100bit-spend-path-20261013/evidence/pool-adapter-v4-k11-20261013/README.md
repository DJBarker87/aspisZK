# Pool adapter v4 k11: local V0 measurements

These files record the frozen NUC build and deterministic LiteSVM measurements for the explicitly authorized k11 adapter experiment. The route remains unproved; the outputs measure one harness path and do not establish protocol security or deployment readiness.

The frozen source revision is `7742957648c33cf045eb6a672e7c7cc796b61087+pool-adapter-v4-k11+9f025c4b8d3077b6c23548aa4215ecd25bc45e301b09a7f532f072a153f8a96c`. The verifier ELF was built with `pool-adapter`; the stripped ELF SHA-256 is `98b59d6ee21491775fe2fdf7bdf60ffa76c96e9f7a2d85f88f56a604addc7c36`, the pristine linked ELF SHA-256 is `62b5e5a49f64c64d81b6b5e159642049a04a2d139619bb12ab8fd64c5a400f50`, and the driver SHA-256 is `3ee7f6411509afdc1748533084a67e8098e58e6afccc617fa698a27da4e41aa3`. The artifact freeze JSON records all three, the feature fingerprint, and build source manifest.

The source-manifest comparison after the audit-tool correction found 372 of 373 frozen selected files unchanged. The sole difference was `scripts/r1_p2_stack_audit.py`, changed after the build to use temporary output paths and assert its inputs remain unchanged. The corrected fresh audit used the pristine linked ELF and measured stripped ELF; both inputs remained unchanged, executable text hashes matched, 277/277 linked functions were reachable in the conservative graph, and all 34 diagnostic functions were absent from the linked ELF with no reachable diagnostics. The earlier mutating-audit copy and its hash are documented in the freeze record; it is retained separately on NUC.

All successful cases used TxV0 and the real 1.4M compute-unit limit, with no diagnostic override. Stage 1 was instruction `[3,11]`; the terminal Pool instruction used the 320-byte ASQ8 request. Transaction sizes include compute-budget instructions and were below the 1,232-byte V0 limit.

| Case | Stage 1 CU | Terminal CU | Terminal Tx bytes | Result |
| --- | ---: | ---: | ---: | --- |
| Transfer, 13 pairs | 1,388,606 | 1,295,281 | 879 | accepted |
| Withdrawal, 13 pairs | 1,387,226 | 1,311,593 | 1,044 | accepted |
| Transfer, 255 pairs | 1,388,608 | 1,361,386 | 912 | accepted |
| Withdrawal, 255 pairs | 1,387,210 | 1,377,495 | 1,077 | accepted |
| Transfer, 1,023 pairs | 1,388,644 | 1,357,996 | 912 | accepted |
| Withdrawal, 1,023 pairs | 1,387,528 | 1,374,341 | 1,077 | accepted |

The 13-pair fixtures reused matching retained S2 sidecars. The 255-pair transfer reused the retained transfer fixture; no matching withdrawal fixture existed, so the frozen driver generated one. Both 1,023-pair fixtures were generated fresh. Sidecars and measured public fixtures are included; task payer and authority key files are excluded from this archive and remain on NUC.

At 1,023 pairs, proof mutation was rejected with `InvalidInstructionData` after 206,944 terminal CU, and the evidence records byte-exact account rollback. Replay at 1,023 pairs was not submitted: the harness requires a same-page history layout and stops at the explicit preflight check `replay/nullifier measurement requires same-page layout`. A 13-pair same-page replay succeeded once and the repeated terminal attempt was rejected after 24,177 CU; the settled state was byte-exact after rejection. At 1,023 pairs, the withdrawal CPI-failure case reached verifier success before an injected test-only failing token-program double rejected the outer transaction; evidence records byte-exact rollback and unchanged vault/destination balances. This injection is not a claim about the real Token Program.

The successful 13-pair transfer evidence also records lifecycle negative checks (tail injection and straddle, wrong authority, repeat init/finalize, post-seal write, malformed candidate/public finalization, and unsealed stage 1); each invoked the program and rolled back. A first attempt using a pre-created output directory stopped at the harness's no-reuse guard before execution; the failed receipt is preserved alongside the successful retry with a fresh, uncreated output path.

`curated-evidence.tar.gz` is the safe NUC archive of the files in this folder except this README, the checksum list, and the archive itself. It includes receipts, logs, build metadata, evidence JSON, and public fixture snapshots. It contains no task key files or ELF binaries. `SHA256SUMS` covers all extracted evidence files and the archive.
