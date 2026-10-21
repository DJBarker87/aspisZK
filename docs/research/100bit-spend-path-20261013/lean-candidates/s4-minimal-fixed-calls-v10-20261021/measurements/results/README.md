# v10 candidate optimized SBF and CU probe

Candidate-only; no frozen-source equivalence or adoption claim. The optimized SBF build passed. All six retained transfer/withdrawal fixtures matched the baseline stage1 checkpoint-tail and return-data hashes, and strict stack audit passed.

| Fixture | Stage1 CU baseline → candidate (delta) | Settlement CU baseline → candidate (delta) |
|---|---:|---:|
| Transfer, 13 | 1,197,177 → 1,210,255 (+13,078) | 1,138,518 → 1,154,207 (+15,689) |
| Transfer, 255 | 1,199,286 → 1,212,366 (+13,080) | 1,169,558 → 1,185,253 (+15,695) |
| Transfer, 1023 | 1,193,428 → 1,206,507 (+13,079) | 1,169,306 → 1,185,005 (+15,699) |
| Withdrawal, 13 | 1,193,569 → 1,206,647 (+13,078) | 1,148,816 → 1,164,505 (+15,689) |
| Withdrawal, 255 | 1,193,699 → 1,206,774 (+13,075) | 1,178,769 → 1,194,471 (+15,702) |
| Withdrawal, 1023 | 1,195,178 → 1,208,258 (+13,080) | 1,176,341 → 1,192,036 (+15,695) |

The highest measured value is 1,212,366 CU, 187,634 below the fixtures' 1,400,000 declared CU limit (86.60%). Mean deltas are +13,078.3 stage1 and +15,694.8 settlement CU. It improves on v8 by about 510 stage1 and 612 settlement CU on average but still costs more than baseline.

Candidate artifact SHA-256: `07dc7c5b77d6eae882f786fee18b8ab8ba922323d425f344a823e8f02e68fff1` (1,509,024 bytes). The build completed in 5.723 s, peak process RSS 203,612 KiB, scope peak 1,043,357,696 bytes, swap 0, and no memory events. Its systemd scope used MemoryHigh 2 GiB, MemoryMax 4 GiB, swap 0. The six fixtures each completed in 0.114–0.164 s, within MemoryMax 1 GiB / MemoryHigh 512 MiB / swap 0. Strict stack completed in 0.064 s.

The baseline comparison is the pinned 58-path source inventory at `b2727acd3abf79315d18b754a260f58f4b1c6326`, checked against current research HEAD `78812cfb5f384933ec3e2bc7eb76580e2672ace4`. 56 entries are byte-identical; `prover.rs` is excluded by the chosen non-prover feature set and `r1_checkpoint_tests.rs` is test-only. This is a completeness-limited source manifest, not an exhaustive reachability proof.

The gate runner generated payer and authority fixture keys. Their contents were not inspected or cleaned up. The original fixture task keys remain on the NUC candidate run. Do not publish or delete them without a separate balance/authority inventory and refund check.
