# Split-10 local cost and compatibility run

This bundle records an isolated candidate that lets the first transaction use
either the existing split-11 instruction `[3, 11]` or split-10 `[3, 10]` and
passes the selected pair count to the same verifier adapter. The total is still
22 query pairs. The SBF ELF is a local cost-probe artifact and is not the
runtime source.

The build used Solana `cargo-build-sbf` 3.1.13 / platform-tools v1.52. SBF and
driver builds ran in user scopes capped at 4 GiB high, 6 GiB maximum, zero
swap, and 128 tasks. The initial optimized-driver build hit the thread limit;
the retained retry used `--jobs 2` and succeeded. An initial gate wrapper also
failed before starting a transaction because its recorder path was wrong; its
time log is retained. Neither failed setup produced a gate result.

All gate runs below reused the retained OS-random-mask proof/public fixtures;
they did not draw new masks. `stage1_compute_units` and `compute_units` are the
whole first and terminal transaction totals respectively. These figures are
not verifier-CPI-only measurements. All successful transactions had matching
simulation and execution results.

| Driver / operation | Pairs | Stage-1 instruction | Stage 1 CU | Terminal CU | Result |
|---|---:|---|---:|---:|---|
| split10 transfer | 13 | `[3, 10]` | 1,342,862 | 1,286,105 | accepted |
| split10 transfer | 255 | `[3, 10]` | 1,342,611 | 1,352,257 | accepted |
| split10 withdrawal | 255 | `[3, 10]` | 1,341,279 | 1,368,461 | accepted |
| split10 transfer | 1023 | `[3, 10]` | 1,342,677 | 1,349,212 | accepted |
| split10 withdrawal | 1023 | `[3, 10]` | 1,341,402 | 1,365,206 | accepted |
| old split11 driver, same ELF | 13 | `[3, 11]` | 1,392,390 | 1,236,579 | accepted |

The 13-pair transfer also exercised uploader lifecycle rejection checks,
including an unsealed stage-1 submission, with rollback. A separate replay
attempt was rejected and preserved the settled state byte-for-byte. The large
withdrawal cases include rollover-history settlement checks. The JSON evidence
contains the transaction, account, and lifecycle assertions for each case.

Proof/public pins, the three-file source diff, source manifests, toolchain
pins, build logs, transaction evidence, timing/resource receipts, and program
artifacts are retained in this directory. `key-retention.txt` records only
paths and permission modes for task keys retained on the NUC; private key
contents are not copied into this evidence bundle.

This is deterministic local LiteSVM evidence. It does not establish protocol
security or proof correctness, and the split10 source has not been adopted.
