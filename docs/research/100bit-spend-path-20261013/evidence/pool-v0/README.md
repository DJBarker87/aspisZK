# TxV0 Pool-path baseline and V2 withdrawal CPI gate

This directory records deterministic LiteSVM measurements using the root-audited lifecycle-v2 cost-probe ELF. It does not establish protocol security or close cryptographic obligations. The harness source snapshot is [`pool_gate-v0.rs`](pool_gate-v0.rs), SHA-256 `8d27529b5168ff1cc95d6e8d54075365288a69767e3581197daca9d63f52d9c1`.

The optimized driver build completed on NUC under `MemoryHigh=4 GiB`, `MemoryMax=6 GiB`, `MemorySwapMax=0`, using the shared cached Cargo target. The final build receipt is [`pool-driver-v0-buildfix5.json`](pool-driver-v0-buildfix5.json); its source revision includes the harness SHA above. The runtime receipts identify the exact earlier harness revision used for the measurements (`pool-driver-v0-6c849b3e…`); the final snapshot changes only the printed transaction-version label and was rebuilt successfully afterward. The evidence JSON records the correct transaction version. Intermediate receipts are retained. `buildfix2` is a failed source-compile attempt with type/API plumbing errors; its log and receipt are preserved. The earlier build attempt without a receipt failed before Cargo started because the non-login shell lacked Cargo on `PATH`. Later successful builds used the pinned shared target and `CARGO_BUILD_JOBS=8`.

| Case | Transaction | Outcome | Stage 1 CU | Terminal CU | Terminal bytes | Upload writes / bytes |
| --- | --- | --- | ---: | ---: | ---: | ---: |
| Transfer, 13 populated pairs | TxV0 | accepted | 1,342,707 | 1,374,664 | 879 / 1,232 max | 157 / 181,790 |
| Withdrawal, 13 populated pairs | TxV0 | accepted | 1,341,346 | 1,390,957 | 1,044 / 1,232 max | 157 / 181,790 |
| Withdrawal with injected CPI failure, 13 pairs | TxV1 | rejected with rollback | 1,340,896 | 1,389,324 | 1,010 / 4,096 max | 140 / 170,859 |

Each V0 case reused its matching v1 proof/public sidecars. TxV0 messages include explicit compute-budget instructions for the 1.4M CU limit, 256 KiB heap, and 8 MiB loaded-account-data limit. They omit a priority-fee instruction. Lifecycle writes use 800-byte chunks to remain within the 1,232-byte serialized transaction limit. V1 behavior remains unchanged at 900-byte chunks and its prior priority-fee configuration.

The CPI-failure case uses a test-only failing program installed at the SPL Token program address. Its trace confirms verifier stage 2 succeeded before the injected token CPI error, and protected accounts rolled back byte-exactly. This tests rollback ordering; it is not a claim about a defect in the real token program.

All run receipts record the NUC host, command, cgroup limits, wall time, RSS, swap, and exit status. Logs and full JSON outputs accompany each receipt. Task directories and retained payer/authority keys remain on NUC and were not copied or cleaned up. Reused executable SHA-256 values: Pool `0e94c98d28437f0b01dce546fdefaad21dc10772a4d46991c2a573d8129cd4f6`, Registry `0f14c7b74ec6cbe3b3f637b0f24c7e8cdc46fd09f5b2e495fd51ada16ad8f11b`, and lifecycle-v2 verifier `c73cfb72515dfd8de491a272999c7a64a2e751f60491da50f952faac4f031d6e`.

Pair-255 rollover was not rerun. Root will run that boundary after the authenticated-parser v3 SBF is ready.

## v3/v3b authenticated-parser check

The first v3 artifact was feature-disabled: its Cargo fingerprint omitted `pool-adapter`, and the attempted lifecycle init `[4, 0]` returned `InvalidInstructionData` after 529 verifier-program CU. No stage 1 or Pool terminal instruction ran. The failed receipt/log are preserved as `pool-transfer-v3-v0-baseline-run.*`; that ELF was not used for later tests.

Corrected v3b was built with `pool-adapter`, the lifecycle symbols were present, and the stack audit passed. The frozen adapter-enabled ELF SHA-256 is `76465ed0432db7cca0559b4f66092a5b5c09d74fb168d29fff7a340bf009ab99`; the frozen harness driver SHA-256 is `e6af6ed149d0d55cca7680cf7365d0f0c381b20f0b9b95c4d3ae3acc89f9d8f9`. The frozen driver's file mode lacked execute permission, so an executable byte-identical copy was used from the dedicated `pool-v0/frozen-driver-copy` NUC directory; original stage bytes were not changed.

With v3b, V0 default-13 transfer and withdrawal passed at 1,344,689 CU (stage 1 1,339,197; 879 transaction bytes) and 1,360,982 CU (stage 1 1,337,836; 1,044 bytes), respectively. Both reused matching v1 proof/public fixtures. The v3b rollover transfer reused the v2-generated 255-pair proof/public with SHA-256 `34a15fdf4c867df60c7c0dcb23092f9c21e33f8d9e35e22955b4a995af3324bd` and `e201be4a028d74258c5344e7395bfabf7568af4ee7df0ec0c7b695f02fbacb15`. It reached verifier `r1:final` but exhausted the 1.4M transaction budget: 2,696 CU remained at the final marker, verifier consumed 1,286,887 of 1,286,943, and Pool consumed 1,399,494 of 1,399,550 before `ProgramFailedToComplete`. The run receipt and phase log are preserved as `pool-transfer-pairs255-v0-v3b-run.*`. No 255-pair withdrawal was started after this CU failure.
