# G_R1.2 — P2 cost reconciliation

Cost accounting only, against the lead review at `ceda7d902`. The selected d18 verifier and both retained adapter ELFs complete the ordinary transfer and withdrawal fixtures at 1.4M CU. None of these complete spend pairs meets the lead's 1.3M-per-transaction bound. No security or deployment conclusion follows.

The tables below use the exact P2 S2 buckets from [REPORT-P2](../../../results/r1-precheck-20261010/REPORT-P2.md). d18 reuses its existing five capped runs. This job adds five fresh runs per operation for each adapter because the retained adapter evidence had only a single run. Every table cell is identical across its five runs. The new full-random-mask d18 measurements are reported separately in [FULL-RANDOM-MASK-CU.md](FULL-RANDOM-MASK-CU.md).

## Accounting conventions

These are **whole-transaction** CU values, with verifier subtotal, outer Pool/custody work and transaction overhead shown separately. Nested CPI totals are not added twice. All raw receipts and reproducible table generation are in [results/gr1-cost-20261013](../../../results/gr1-cost-20261013/README.md); [gr1/reconcile.py](gr1/reconcile.py) checks every sum and five-run equality.

Markers report remaining CU after each named stage. A bucket is the preceding interval, including marker overhead. Semantic/query submarkers are accumulated into their P2 buckets. Checkpoint write includes account-copy/status-update intervals. Entry/exit is the residual needed to match the logged verifier consumption.

Two boundaries need care. Adapter tx1 has no entry marker: its Parse bucket includes entry, sealed-account checks, candidate checks and public decoding before strict proof parsing; its Entry/exit cell contains the exit tail only. Adapter tx2's Parse bucket includes account/registry/statement reconstruction between `pool-adapter-stage2-begin` and `parsed`. These existing ELFs do not expose finer separation. No unmeasured parser-only number is inferred.

The v2 column uses the original TxV1 path; v3b uses the corrected TxV0 path. Their non-program overhead is 56 versus 506 CU. The lead review's v2 totals are 450 CU higher than the raw TxV1 receipts: they equal raw TxV1 CU plus three 150-CU compute-budget instructions from a TxV0 envelope. The actual v2 receipt totals are used here, with the 450-CU distinction explicit; it is not an arithmetic saving. This discrepancy does not change any 1.3M-bound outcome.

### Transfer tx1

| Phase (CU) | P2 S2 | d18 | Adapter v2 (TxV1) | Adapter v3b (TxV0) | P2 − d18 |
| --- | ---: | ---: | ---: | ---: | ---: |
| Parse | 56,875 | 45,843 | 58,172 | 54,662 | +11,032 |
| Semantic | 903,170 | 566,414 | 566,248 | 566,248 | +336,756 |
| Prepare | 489,141 | 155,355 | 155,379 | 155,379 | +333,786 |
| Checkpoint read | 0 | 0 | 0 | 0 | +0 |
| Merkle | 100,280 | 108,318 | 108,404 | 108,404 | -8,038 |
| Query folds and rho accumulation | 822,065 | 386,845 | 386,817 | 386,817 | +435,220 |
| Relation rounds and pairing | 0 | 0 | 0 | 0 | +0 |
| Final rho | 0 | 0 | 0 | 0 | +0 |
| Checkpoint write | 68,211 | 67,126 | 67,128 | 67,128 | +1,085 |
| Entry/exit | 1,309 | 1,309 | 53 | 53 | +0 |
| Verifier subtotal | 2,441,051 | 1,331,210 | 1,342,201 | 1,338,691 | +1,109,841 |
| Pool/custody outside verifier | 0 | 0 | 0 | 0 | +0 |
| Transaction overhead | 356 | 356 | 56 | 506 | +0 |
| Whole transaction | 2,441,407 | 1,331,566 | 1,342,257 | 1,339,197 | +1,109,841 |

### Transfer tx2

| Phase (CU) | P2 S2 | d18 | Adapter v2 (TxV1) | Adapter v3b (TxV0) | P2 − d18 |
| --- | ---: | ---: | ---: | ---: | ---: |
| Parse | 36,136 | 30,385 | 63,757 | 33,782 | +5,751 |
| Semantic | 0 | 0 | 0 | 0 | +0 |
| Prepare | 0 | 0 | 0 | 0 | +0 |
| Checkpoint read | 114,865 | 107,357 | 107,367 | 107,367 | +7,508 |
| Merkle | 120,355 | 129,876 | 129,920 | 129,920 | -9,521 |
| Query folds and rho accumulation | 983,707 | 463,946 | 463,991 | 463,991 | +519,761 |
| Relation rounds and pairing | 1,059,165 | 526,890 | 526,890 | 526,890 | +532,275 |
| Final rho | 94,175 | 20,962 | 20,962 | 20,962 | +73,213 |
| Checkpoint write | 1,783 | 1,267 | 0 | 0 | +516 |
| Entry/exit | 1,306 | 1,306 | 7,780 | 7,780 | +0 |
| Verifier subtotal | 2,411,492 | 1,281,989 | 1,320,667 | 1,290,692 | +1,129,503 |
| Pool/custody outside verifier | 0 | 0 | 53,491 | 53,491 | +0 |
| Transaction overhead | 356 | 356 | 56 | 506 | +0 |
| Whole transaction | 2,411,848 | 1,282,345 | 1,374,214 | 1,344,689 | +1,129,503 |

### Withdrawal tx1

| Phase (CU) | P2 S2 | d18 | Adapter v2 (TxV1) | Adapter v3b (TxV0) | P2 − d18 |
| --- | ---: | ---: | ---: | ---: | ---: |
| Parse | 56,823 | 45,791 | 58,063 | 54,553 | +11,032 |
| Semantic | 899,866 | 565,114 | 565,063 | 565,063 | +334,752 |
| Prepare | 489,020 | 155,356 | 155,341 | 155,341 | +333,664 |
| Checkpoint read | 0 | 0 | 0 | 0 | +0 |
| Merkle | 100,222 | 108,462 | 108,360 | 108,360 | -8,240 |
| Query folds and rho accumulation | 819,546 | 386,805 | 386,832 | 386,832 | +432,741 |
| Relation rounds and pairing | 0 | 0 | 0 | 0 | +0 |
| Final rho | 0 | 0 | 0 | 0 | +0 |
| Checkpoint write | 68,211 | 67,126 | 67,128 | 67,128 | +1,085 |
| Entry/exit | 1,309 | 1,309 | 53 | 53 | +0 |
| Verifier subtotal | 2,434,997 | 1,329,963 | 1,340,840 | 1,337,330 | +1,105,034 |
| Pool/custody outside verifier | 0 | 0 | 0 | 0 | +0 |
| Transaction overhead | 356 | 356 | 56 | 506 | +0 |
| Whole transaction | 2,435,353 | 1,330,319 | 1,340,896 | 1,337,836 | +1,105,034 |

### Withdrawal tx2

| Phase (CU) | P2 S2 | d18 | Adapter v2 (TxV1) | Adapter v3b (TxV0) | P2 − d18 |
| --- | ---: | ---: | ---: | ---: | ---: |
| Parse | 36,136 | 30,385 | 63,696 | 33,721 | +5,751 |
| Semantic | 0 | 0 | 0 | 0 | +0 |
| Prepare | 0 | 0 | 0 | 0 | +0 |
| Checkpoint read | 114,779 | 107,357 | 107,342 | 107,342 | +7,422 |
| Merkle | 120,480 | 129,882 | 129,948 | 129,948 | -9,402 |
| Query folds and rho accumulation | 986,011 | 463,860 | 464,010 | 464,010 | +522,151 |
| Relation rounds and pairing | 1,059,243 | 526,930 | 527,061 | 527,061 | +532,313 |
| Final rho | 94,148 | 20,962 | 20,962 | 20,962 | +73,186 |
| Checkpoint write | 1,783 | 1,267 | 0 | 0 | +516 |
| Entry/exit | 1,306 | 1,306 | 7,773 | 7,773 | +0 |
| Verifier subtotal | 2,413,886 | 1,281,949 | 1,320,792 | 1,290,817 | +1,131,937 |
| Pool/custody outside verifier | 0 | 0 | 69,659 | 69,659 | +0 |
| Transaction overhead | 356 | 356 | 56 | 506 | +0 |
| Whole transaction | 2,414,242 | 1,282,305 | 1,390,507 | 1,360,982 | +1,131,937 |

## Where the savings occur

The following ledger assigns every CU delta, including regressions, to a named compiled stage. It is a stage accounting attribution, not an isolated single-function microbenchmark. Inputs are P2 proof/public bytes through `geometry-dots`; d18 changes transport and regenerates the proof. Transfer uses retained stage diagnostics. Withdrawal's missing earlier-stage diagnostics were run under the same 4G/6G/swap-0 caps with the retained ELFs and the matching old/new checkpoint-layout drivers.

### Transfer stage attribution

| Phase | P2 → pairing | → terminal | → rho-clean | → geometry-dots | → D18 transport + regenerated proof | Total P2 → d18 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| tx1 Parse | +5,752 | +0 | +5,280 | +0 | +0 | +11,032 |
| tx1 Semantic | +95,146 | +238,509 | +2,924 | +0 | +177 | +336,756 |
| tx1 Prepare | +332,733 | +0 | +971 | +2 | +80 | +333,786 |
| tx1 Checkpoint read | +0 | +0 | +0 | +0 | +0 | +0 |
| tx1 Merkle | -20 | +0 | -19 | -8,089 | +90 | -8,038 |
| tx1 Query folds and rho accumulation | +245,289 | +0 | +101,411 | +88,550 | -30 | +435,220 |
| tx1 Relation rounds and pairing | +0 | +0 | +0 | +0 | +0 | +0 |
| tx1 Final rho | +0 | +0 | +0 | +0 | +0 | +0 |
| tx1 Checkpoint write | +600 | +0 | +491 | -6 | +0 | +1,085 |
| tx1 Entry/exit | +0 | +0 | +0 | +0 | +0 | +0 |
| tx1 Verifier subtotal | +679,500 | +238,509 | +111,058 | +80,457 | +317 | +1,109,841 |
| tx1 Pool/custody outside verifier | +0 | +0 | +0 | +0 | +0 | +0 |
| tx1 Transaction overhead | +0 | +0 | +0 | +0 | +0 | +0 |
| tx1 Whole transaction | +679,500 | +238,509 | +111,058 | +80,457 | +317 | +1,109,841 |
| tx2 Parse | +5,752 | +0 | +0 | -1 | +0 | +5,751 |
| tx2 Semantic | +0 | +0 | +0 | +0 | +0 | +0 |
| tx2 Prepare | +0 | +0 | +0 | +0 | +0 | +0 |
| tx2 Checkpoint read | +6,236 | +0 | +1,241 | +0 | +31 | +7,508 |
| tx2 Merkle | -36 | +0 | -12 | -9,488 | +15 | -9,521 |
| tx2 Query folds and rho accumulation | +291,634 | +0 | +121,903 | +106,246 | -22 | +519,761 |
| tx2 Relation rounds and pairing | +531,611 | +0 | +0 | +1 | +663 | +532,275 |
| tx2 Final rho | +58,160 | +0 | +15,053 | +0 | +0 | +73,213 |
| tx2 Checkpoint write | -3 | +0 | +528 | -9 | +0 | +516 |
| tx2 Entry/exit | +0 | +0 | +0 | +0 | +0 | +0 |
| tx2 Verifier subtotal | +893,354 | +0 | +138,713 | +96,749 | +687 | +1,129,503 |
| tx2 Pool/custody outside verifier | +0 | +0 | +0 | +0 | +0 | +0 |
| tx2 Transaction overhead | +0 | +0 | +0 | +0 | +0 | +0 |
| tx2 Whole transaction | +893,354 | +0 | +138,713 | +96,749 | +687 | +1,129,503 |

### Withdrawal stage attribution

| Phase | P2 → pairing | → terminal | → rho-clean | → geometry-dots | → D18 transport + regenerated proof | Total P2 → d18 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| tx1 Parse | +5,752 | +0 | +5,280 | +0 | +0 | +11,032 |
| tx1 Semantic | +95,145 | +236,615 | +2,924 | +0 | +68 | +334,752 |
| tx1 Prepare | +332,679 | +0 | +971 | +2 | +12 | +333,664 |
| tx1 Checkpoint read | +0 | +0 | +0 | +0 | +0 | +0 |
| tx1 Merkle | -20 | +0 | -19 | -8,087 | -114 | -8,240 |
| tx1 Query folds and rho accumulation | +242,731 | +0 | +101,497 | +88,457 | +56 | +432,741 |
| tx1 Relation rounds and pairing | +0 | +0 | +0 | +0 | +0 | +0 |
| tx1 Final rho | +0 | +0 | +0 | +0 | +0 | +0 |
| tx1 Checkpoint write | +600 | +0 | +491 | -6 | +0 | +1,085 |
| tx1 Entry/exit | +0 | +0 | +0 | +0 | +0 | +0 |
| tx1 Verifier subtotal | +676,887 | +236,615 | +111,144 | +80,366 | +22 | +1,105,034 |
| tx1 Pool/custody outside verifier | +0 | +0 | +0 | +0 | +0 | +0 |
| tx1 Transaction overhead | +0 | +0 | +0 | +0 | +0 | +0 |
| tx1 Whole transaction | +676,887 | +236,615 | +111,144 | +80,366 | +22 | +1,105,034 |
| tx2 Parse | +5,752 | +0 | +0 | -1 | +0 | +5,751 |
| tx2 Semantic | +0 | +0 | +0 | +0 | +0 | +0 |
| tx2 Prepare | +0 | +0 | +0 | +0 | +0 | +0 |
| tx2 Checkpoint read | +6,179 | +0 | +1,241 | +0 | +2 | +7,422 |
| tx2 Merkle | -36 | +0 | -12 | -9,480 | +126 | -9,402 |
| tx2 Query folds and rho accumulation | +294,202 | +0 | +121,724 | +106,192 | +33 | +522,151 |
| tx2 Relation rounds and pairing | +531,753 | +0 | +0 | +1 | +559 | +532,313 |
| tx2 Final rho | +58,132 | +0 | +15,054 | +0 | +0 | +73,186 |
| tx2 Checkpoint write | -3 | +0 | +528 | -9 | +0 | +516 |
| tx2 Entry/exit | +0 | +0 | +0 | +0 | +0 | +0 |
| tx2 Verifier subtotal | +895,979 | +0 | +138,535 | +96,703 | +720 | +1,131,937 |
| tx2 Pool/custody outside verifier | +0 | +0 | +0 | +0 | +0 | +0 |
| tx2 Transaction overhead | +0 | +0 | +0 | +0 | +0 | +0 |
| tx2 Whole transaction | +895,979 | +0 | +138,535 | +96,703 | +720 | +1,131,937 |

| Named stage | Work responsible for the measured buckets | Mechanical equivalence coverage |
| --- | --- | --- |
| `pairing` | WideExact mixed-field dot/pairing kernels, prepared weights and field/sampler/domain changes; validated semantic-prefix reuse. Savings appear in semantic, prepare, query and relation/final pairing, plus parse/checkpoint decoding. | `dot_accumulators_match_core_products_at_boundary_lengths`, `batched_dots_match_the_frozen_verifier`, domain/line-node exhaustive tests, both sampler-equivalence tests, `optimized_pair_matches_raw_dual_expression_for_all_variants`, validated-prefix/transcript tests. Historical `pairing-test` receipt retained. |
| `terminal` | Enables the nine existing optimized-terminal feature kernels. All measured savings are in tx1 semantic evaluation. | Historical `terminal-test` receipt and dense semantic/challenge trace comparison in the native gates. No semantic verification moved to tx2. |
| `rho-clean` | QM31 rho/accumulator weights replace the earlier WideExact representation; mixed-field accumulation and checkpoint representation change. Checkpoint shrinks from 2,824 to 1,768 bytes. Semantic parsing also uses the validated prefix. | Full challenge/weight/check trace equality against the corresponding dense implementation; pairing/weights/prefix tests. This is a changed field choice with an updated reference, **not** evidence that the old and new challenge distributions are equivalent. |
| `geometry-dots` | Batch-inverts five denominators per query once per transaction; reuses mixed-field query dots. | `batched_geometry_inverses_match_individual_inverses_for_ranges`, `batched_circle_and_line_folds_match_independent_reference`, dot tests. The one-time geometry setup occurs after Prepare/CheckpointRead and before the first Merkle marker: its cost moved into that first Merkle interval. Increased Merkle-bucket CU therefore does not mean increased Merkle hashing. |
| `d18` | Changes coefficient-to-row transport to digit permutation `[3,4,2,0,1]`; matching point weights/dense reference and proof regeneration. Small deltas span semantic, prepare/read, query, relation and branch-dependent hashing. | `s_transport_is_a_bijection_and_matches_documented_pi_inverse`, `s1_s2_point_weights_match_independent_row_eq_products`, weights tests and 10,699-entry dense trace agreement on each d18 fixture. The combined transport/input delta cannot be represented as a same-proof optimization. |
| `adapter-v2` | Adds the sealed proof/public lifecycle and account/candidate/registry/Pool statement reconstruction around the d18 verifier. Pool settlement and withdrawal custody are outside the verifier subtotal. | Existing lifecycle/mutation receipts and each new transfer run's nine lifecycle negative cases, unchanged proof/public/checkpoint checks, simulation/execution equality and expected afterstate bytes. The native arithmetic checks cover the verifier, not a formal source/runtime correspondence. |
| `adapter-v3b` | Relative to v2, tx2's Parse interval drops 29,975 CU on both operations after authenticated parsing; tx1's combined entry/Parse interval drops 3,510 CU. All other verifier buckets are identical. The source/build transition also contains adapter stack/decoding changes, so 3,510 is attributed to the compiled adapter prefix, not to a uniquely isolated function. | New strict/authenticated tx2 trace equality and targeted corpus; lifecycle negative cases; v3b frozen source and stack audit. The skipped scan was performed by tx1 over **all** proof fields, including queries deferred to tx2. Account reconstruction remains in tx2 Parse. |

[adapter-dense-result.json](../../../results/gr1-cost-20261013/adapter-dense-result.json) additionally checks the exact transfer/withdrawal proof bytes used in both adapter columns: 10,699 native/dense and 9,253 strict/authenticated tx2 entries match for each.

The frozen v3b release test suite passed all 15 tests in these categories; [equivalence.log](../../../results/gr1-cost-20261013/equivalence.log) names each test. Full-mask positive cases add exact equality of 10,699 native/dense trace entries and 9,253 strict/authenticated tx2 entries per operation. [AUTHENTICATED-TX2.md](AUTHENTICATED-TX2.md) gives the covering argument and 5,675-case-per-operation corpus.

Adapter tx2 writes no checkpoint status: its checkpoint is read-only, and successful Pool settlement consumes the nullifier. The standalone harness writes status/checksum after strict tx2; this accounts for its Checkpoint write bucket and does not migrate the write to another verifier phase. Adapter return encoding is in Entry/exit; actual lane/history/nullifier/token work is in Pool/custody outside verifier.

### Retained incompatibility diagnostic

The additional withdrawal diagnostic using the **old P2 proof** against d18 completed tx1 and rejected tx2 at `Relation` (`InstructionError(2, InvalidInstructionData)`). Receipt: [withdrawal-stage-d18.json](../../../results/gr1-cost-20261013/withdrawal-stage-d18.json). It is retained as a failed compatibility check, not counted as a completed CU measurement. The attribution table uses d18's five successful regenerated-proof runs for its last column. The old proof is accepted by pairing, terminal, rho-clean and geometry-dots. Thus neither the rho-field change nor the D18 transition should be described as an end-to-end P2 security-equivalence proof.

## Pinned artifacts and receipts

| Artifact | SHA-256 |
| --- | --- |
| P2 S2 ELF | `1ec08e2381f401900f7d78fadb688e28b50ffd25395d3d478164b82436283457` |
| Selected d18 ELF | `48857d754accece121046c5e0ceaa79d49fbbe22e89f1bdda55d08f66ef84a9a` |
| Adapter v2 ELF | `c73cfb72515dfd8de491a272999c7a64a2e751f60491da50f952faac4f031d6e` |
| Adapter v3b ELF | `76465ed0432db7cca0559b4f66092a5b5c09d74fb168d29fff7a340bf009ab99` |
| Frozen adapter harness | `e6af6ed149d0d55cca7680cf7365d0f0c381b20f0b9b95c4d3ae3acc89f9d8f9` |
| Standalone d18 CU harness | `6e26391f3558902b53b8083d2798fb78f5f81bd0132627e4b21932670c33f1e3` |

The d18 source file-map hash is `f75e70d832444fd562d3ffb000f37e2f0b1c06f7940a2334f04457011e17e8be`; v3b's is `a810048410e72612d757353f53555b8c586115a13b519060989ed6ab533733f2`. Its source archive hash is `a83d14848d37e20d26bcfb5c80e6599446aa3bf27895f03fa1cfd5fedefb696a`. Native work used that isolated archive with its members hash-checked unchanged. The v2 historical build receipt has a revision label rather than a complete source-file manifest; the exact retained ELF, its build/stack receipts and all new input hashes are preserved. No replacement v2 ELF was built.

Every new run has a separate resource receipt (command, exit, wall, RSS, cgroup peak/swap) and input-hash record. All scopes used MemoryHigh 4 GiB, MemoryMax 6 GiB, MemorySwapMax 0. The receipt `source_revision` is the G_R1 runner/frozen-native-source label; each measured ELF's identity is its command/input hash and the artifact mapping above, not that shared runner label. See the [evidence audit](../../../results/gr1-cost-20261013/evidence-audit.json) for the complete run inventory and repairs. No ELF or key is committed.
