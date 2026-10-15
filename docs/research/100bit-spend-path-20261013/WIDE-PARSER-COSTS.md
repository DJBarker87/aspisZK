# Wide parser CU and byte comparison

This note collects local LiteSVM measurements from the preserved v1.52 reuse gates. The phase comparison uses the same 13-pair TxV0 proof/public fixture for all four candidates. The stage1 phase values below are derived only from the recorded program logs: each `Program consumption: … units remaining` value is subtracted from the logged 1,399,550-unit program budget. The first row is cumulative from verifier entry; following rows are differences between consecutive log checkpoints. These checkpoint windows are not isolated function costs.

The phase data distinguishes a completed stage1 execution metric from a failed program budget report. Half `d` and inline `g` stop after the `r1:query:10` marker; they have no completed stage1 transaction CU/byte metric and no terminal measurement. Their final `1,399,494 / 1,399,550` is the failed program-reported consumption, not a successful transaction CU. Baseline and h2 reach `r1:checkpoint-write` and the pool-adapter checkpoint marker.

## Source and input pins

All four 13-pair comparisons reused the same full-OS proof `86d4212e675b36ebd556ca2b08b1b5e554cae15e77dfcd74c93a6f419129ed7c` and public input `f6bcd49446f1077d2c5ed4be940e91f0be444efc5ae83024ec0700b8c205c331`. The shared driver, pool, and registry pins are in each cost bundle. The observed source and ELF pins are:

| Candidate | Field source SHA-256 | Wide source SHA-256 | ELF SHA-256 | Gate/build evidence |
|---|---|---|---|---|
| Baseline accepted | `28df5a1abee13bde4b3aa9eeceb0489bedf00531f298460954a97661f5f1baea` | `56c26ce33cd0caee95f33474bfc351c5409503b6af665dba7c8837d6ec1068ea` | `fca47fb42d1123116ba34b0da5a2af05af0897cfb0f92224ec01885aac56bea8` | [gate](evidence/parser-candidate-v152-cost-20261014/v152-candidate-reuse-evidence.json), [SBF manifest](evidence/parser-candidate-v152-sbf-20261014/manifest.json) |
| Half parser `d` (failed) | `28df5a1abee13bde4b3aa9eeceb0489bedf00531f298460954a97661f5f1baea` | `940e31f8056b6a3b9422d3fa31ae6cbe3c4084d79885bb8fd5b4a14c56dd7d06` | `a12e57d6f4c0298543c615968f412cdb6e4d6e5e0a091ca85850c9de93c137be` | [phase comparison](evidence/wide-parser-v152-cost-20261015/results/phase-cost-comparison.json), [cost manifest](evidence/wide-parser-v152-cost-20261015/manifest.json), [SBF manifest](evidence/wide-parser-v152-sbf-20261015/manifest.json) |
| Inline parser `g` (failed) | `9b9cda686b9051b36f35107fda334dfa4e6f0ccb70b82b27a1108c38b5ada7f0` | `940e31f8056b6a3b9422d3fa31ae6cbe3c4084d79885bb8fd5b4a14c56dd7d06` | `bbaf09e1c43d96cfcff88ea4e47e82bc4f67b9945d5f10861b45d10bf33fd4fe` | [resource record](evidence/wide-parser-inline-v152-cost-20261015/results/wide-inline-v152-reuse-run.json), [gate log](evidence/wide-parser-inline-v152-cost-20261015/results/wide-inline-v152-reuse-run.log), [SBF build](evidence/wide-parser-inline-v152-sbf-20261015/README.md) |
| Selected h2 (accepted) | `28df5a1abee13bde4b3aa9eeceb0489bedf00531f298460954a97661f5f1baea` | `6260fa9d179328714e7df59640abb7a76a326e98900993ce7d3da98c6411d10b` | `ea9be844a7027f613cf310c5fedd54c8db9e6d669ba325af46d3b5908ef43796` | [gate evidence](evidence/wide-parser-unrolled-v152-cost-20261015/results/evidence.json), [cost manifest](evidence/wide-parser-unrolled-v152-cost-20261015/manifest.json), [SBF manifest](evidence/wide-parser-unrolled-v152-sbf-20261015/manifest.json) |

All four used Solana `cargo-build-sbf` 3.1.13 / platform-tools v1.52 / rustc 1.89.0. The h2 source snapshot has base revision `aba310f1daa065a27da89d15c6c47166037a8a71`; candidate source files and build manifest are linked above.

## Logged stage1 checkpoint windows

Values are consumed-CU differences between logged checkpoints, except `r1:parsed`, which is cumulative from verifier entry. Dashes mean the failed run did not reach that checkpoint.

| Logged checkpoint/window | Baseline fca47 | Half `d` a12e57 | Inline `g` bbaf09 | h2 ea9be8 |
|---|---:|---:|---:|---:|
| `r1:parsed` (entry to first checkpoint) | 54,662 | 61,915 | 71,316 | 55,748 |
| `r1:semantic` (delta since preceding checkpoint) | 566,457 | 581,448 | 606,742 | 566,457 |
| `r1:prepare` (delta since preceding checkpoint) | 155,373 | 156,374 | 157,360 | 155,272 |
| `r1:merkle:0` (delta since preceding checkpoint) | 18,807 | 18,807 | 18,807 | 18,807 |
| `r1:query:0` (delta since preceding checkpoint) | 38,830 | 38,969 | 39,444 | 38,946 |
| `r1:merkle:1` (delta since preceding checkpoint) | 10,090 | 10,090 | 10,090 | 10,090 |
| `r1:query:1` (delta since preceding checkpoint) | 38,763 | 38,902 | 39,376 | 38,878 |
| `r1:merkle:2` (delta since preceding checkpoint) | 10,067 | 10,067 | 10,067 | 10,067 |
| `r1:query:2` (delta since preceding checkpoint) | 38,660 | 38,799 | 39,275 | 38,777 |
| `r1:merkle:3` (delta since preceding checkpoint) | 10,066 | 10,066 | 10,066 | 10,066 |
| `r1:query:3` (delta since preceding checkpoint) | 38,655 | 38,794 | 39,268 | 38,770 |
| `r1:merkle:4` (delta since preceding checkpoint) | 10,062 | 10,062 | 10,062 | 10,062 |
| `r1:query:4` (delta since preceding checkpoint) | 38,643 | 38,782 | 39,256 | 38,758 |
| `r1:merkle:5` (delta since preceding checkpoint) | 10,076 | 10,076 | 10,076 | 10,076 |
| `r1:query:5` (delta since preceding checkpoint) | 38,632 | 38,771 | 39,246 | 38,748 |
| `r1:merkle:6` (delta since preceding checkpoint) | 10,066 | 10,066 | 10,066 | 10,066 |
| `r1:query:6` (delta since preceding checkpoint) | 38,633 | 38,772 | 39,247 | 38,749 |
| `r1:merkle:7` (delta since preceding checkpoint) | 10,053 | 10,053 | 10,053 | 10,053 |
| `r1:query:7` (delta since preceding checkpoint) | 38,652 | 38,791 | 39,266 | 38,768 |
| `r1:merkle:8` (delta since preceding checkpoint) | 10,056 | 10,056 | 10,056 | 10,056 |
| `r1:query:8` (delta since preceding checkpoint) | 38,645 | 38,784 | 39,259 | 38,761 |
| `r1:merkle:9` (delta since preceding checkpoint) | 10,052 | 10,052 | 10,052 | 10,052 |
| `r1:query:9` (delta since preceding checkpoint) | 38,663 | 38,802 | 39,276 | 38,778 |
| `r1:merkle:10` (delta since preceding checkpoint) | 10,068 | 10,068 | 10,068 | 10,068 |
| `r1:query:10` (delta since preceding checkpoint) | 38,654 | 38,793 | 39,268 | 38,770 |
| `r1:checkpoint-write` (delta since preceding checkpoint) | 67,906 | — | — | 67,906 |
| `r1:pool-adapter-stage1-checkpoint-written` (delta since preceding checkpoint) | 278 | — | — | 278 |

## Completed transaction measurements

| Candidate | Stage1 transaction CU / bytes | Stage1 program-log completion | Terminal transfer CU / bytes | Terminal byte headroom vs 1,232 B | Observed result |
|---|---:|---:|---:|---:|---|
| Baseline fca47 | 1,390,128 / 295 | 1,389,622 / 1,399,550 | 1,293,571 / 879 | 353 B | Accepted; settlement recorded |
| Half `d` a12e57 | no completed metric / no bytes | 1,399,494 / 1,399,550; failed | not reached | — | Stage1 `ComputationalBudgetExceeded`; exit 1 |
| Inline `g` bbaf09 | no completed metric / no bytes | 1,399,494 / 1,399,550; failed | not reached | — | Stage1 `ComputationalBudgetExceeded`; exit 1 |
| h2 ea9be8 | 1,392,386 / 295 | 1,391,880 / 1,399,550 | 1,303,475 / 879 | 353 B | Accepted; settlement recorded |

The h2 minus baseline arithmetic for this same-fixture gate is +2,258 stage1 transaction CU, +9,904 terminal transaction CU, +12,162 across both measured transactions, and zero terminal-byte difference. At the last common checkpoint `r1:query:10`, h2 is +2,258 log-consumed CU relative to baseline. Its logged Merkle windows match baseline, while each of the eleven query windows is 115–117 CU higher; other earlier checkpoint differences offset some of that query-window sum. These figures describe the recorded checkpoints and transactions; they do not attribute cost to a particular source expression.

At `r1:query:10`, half `d` is +24,774 cumulative log CU relative to baseline and inline `g` is +65,677. Both logs then end with a budget-exceeded program report at 1,399,494 of 1,399,550. No stage1 transaction size, terminal transaction, or settlement should be inferred from those failed runs.

## Larger retained full-mask cases

The next table summarizes the four 255/1,023-pair explicit-reuse runs against h2. Each row uses the exact prior proof/public fixture listed by full hash in the [large-case manifest](evidence/wide-parser-unrolled-large-cases-20261015/large-cases-manifest.json). The original P3 records identify the fixtures as OS `getrandom` full-mask cases. The h2 reruns reused them; they did not generate new proofs or masks. Historical P3 CUs are shown only as arithmetic context: those earlier runs used a different verifier ELF (`c94675d0f0682170ed9288e31feb31c76669f9698c554c36e9978c9a98835ab5`), so their deltas are not an isolated h2-versus-baseline comparison.

| Case | Reused proof SHA-256 | Historical P3 stage1 / terminal CU | h2 stage1 / terminal CU | Arithmetic delta | Terminal bytes / headroom (1,232 B) | Settlement |
|---|---|---:|---:|---:|---:|---|
| transfer 255 | `3d68309b72bf61f0cd36e02b49b4c7d3f8377df81dd7c9b24a25e44ba722908e` | 1,389,907 / 1,359,784 | 1,392,164 / 1,369,686 | +2,257 / +9,902 | 912 B / 320 B | rollover settled; successful |
| withdrawal 255 | `dd83a7260a3a619cbe712ec591574ac625c0a38980c4c81ff6d3b26f8e13b853` | 1,388,574 / 1,375,920 | 1,390,833 / 1,385,823 | +2,259 / +9,903 | 1077 B / 155 B | rollover settled; successful |
| transfer 1023 | `8569435667420b36a980493477f8fef7ef47e7351122647cf3747054079d4d62` | 1,389,978 / 1,356,607 | 1,392,237 / 1,366,505 | +2,259 / +9,898 | 912 B / 320 B | rollover settled; successful |
| withdrawal 1023 | `7bab9c8b102e6527118c589c984ef2b575bb046f18eaab4dc9c2926ec27d36f2` | 1,388,652 / 1,372,691 | 1,390,915 / 1,382,595 | +2,263 / +9,904 | 1077 B / 155 B | rollover settled; successful |

Each larger case had a 295-byte stage1 transaction (937 B headroom against 1,232 B). Transfer terminal transactions were 912 B (320 B headroom); withdrawal terminal transactions were 1,077 B (155 B headroom). All four ran with 256 history roots before the operation; recorded rollover page, history, lane, and marker settlement checks passed. Exact logs, resource receipts, original proof/public bytes, and original P3 provenance records are retained in the [large-case bundle](evidence/wide-parser-unrolled-large-cases-20261015/README.md).

These are local cost and settlement observations for the unproved R1 cost-probe path. They do not make a cryptographic or source-equivalence claim.
