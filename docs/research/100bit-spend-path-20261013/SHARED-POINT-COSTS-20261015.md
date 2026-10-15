# Shared-point contraction cost measurements — 2026-10-15

This compares the isolated shared-point `weights.rs` candidate with the selected h2 unrolled WideExact parser on the same five retained P3 transfer/withdrawal fixtures. These are local SBF/LiteSVM cost observations; they do not prove compiler correctness, universal cost, or semantic equivalence.

## Pins and measurement setup

Both builds use source base `aba310f1daa065a27da89d15c6c47166037a8a71`, the same `field.rs` (`28df5a1abee13bde4b3aa9eeceb0489bedf00531f298460954a97661f5f1baea`), pool program (`0e94c98d28437f0b01dce546fdefaad21dc10772a4d46991c2a573d8129cd4f6`) and registry program (`0f14c7b74ec6cbe3b3f637b0f24c7e8cdc46fd09f5b2e495fd51ada16ad8f11b`). Both use Solana `cargo-build-sbf` 3.1.13 / platform-tools v1.52 / rustc 1.89.0 and the same pinned `pool_gate` driver (`e7e4e20dd01e899965ee6286b2adcdb424e6fa9ba0e033449af7090ba6a03199`).

Relative to the frozen baseline, the shared-point candidate changes only `weights.rs` (baseline `eb55a5a954f611828f03615a837a9298352a44a1c799a3e7726f8e1421c8d81a` → candidate below); h2 changes only `wide_exact.rs` (baseline `56c26ce33cd0caee95f33474bfc351c5409503b6af665dba7c8837d6ec1068ea` → candidate below). The two candidates were built separately.

| Candidate source / ELF | Source SHA-256 | Verifier ELF SHA-256 | ELF bytes |
|---|---|---|---:|
| Shared-point `weights.rs` | `68c9087712ff6bfb08c7ed41a1281798466e6671800761c80f83126963262f63` | `7cf2fb3e7fe3a1237d508b0d3a2629d8cf1229ebf0e22c39ab236cd9a9dd255a` | 1,248,240 |
| h2 `wide_exact.rs` | `6260fa9d179328714e7df59640abb7a76a326e98900993ce7d3da98c6411d10b` | `ea9be844a7027f613cf310c5fedd54c8db9e6d669ba325af46d3b5908ef43796` | 1,216,104 |

The shared-point run results are in [`shared-point-contraction-v152`](evidence/shared-point-contraction-v152-20261015/README.md); h2 results are in [`wide-parser-unrolled-v152-cost`](evidence/wide-parser-unrolled-v152-cost-20261015/manifest.json). The phase values are differences between consecutive program-log checkpoints, following [`WIDE-PARSER-COSTS.md`](WIDE-PARSER-COSTS.md). The selected 13-pair run reused the same proof (`86d4212e675b36ebd556ca2b08b1b5e554cae15e77dfcd74c93a6f419129ed7c`) and public ASF8 (`f6bcd49446f1077d2c5ed4be940e91f0be444efc5ae83024ec0700b8c205c331`) for both verifier ELFs.

## 13-pair terminal phase windows

The exact logs are `shared-point-contraction-v152-20261015/results/evidence-b.json` and `wide-parser-unrolled-v152-cost-20261015/results/evidence.json`, under each record's `execution.logs`. Values below are consumed CU between the named markers; the first interval begins at the logged `r1:pool-adapter-stage2-begin` checkpoint. Negative delta means the shared-point candidate consumed less.

| Stage-2 checkpoint interval | Shared-point CU | h2 CU | Shared-point minus h2 |
|---|---:|---:|---:|
| stage2-begin → parsed | 32,282 | 32,282 | 0 |
| parsed → checkpoint-read | 108,412 | 108,412 | 0 |
| checkpoint-read → merkle:11 | 18,806 | 18,806 | 0 |
| merkle:11 → query:11 | 38,784 | 38,784 | 0 |
| query:11 → merkle:12 | 10,065 | 10,065 | 0 |
| merkle:12 → query:12 | 38,778 | 38,778 | 0 |
| query:12 → merkle:13 | 10,086 | 10,086 | 0 |
| merkle:13 → query:13 | 38,755 | 38,755 | 0 |
| query:13 → merkle:14 | 10,088 | 10,088 | 0 |
| merkle:14 → query:14 | 38,777 | 38,777 | 0 |
| query:14 → merkle:15 | 10,074 | 10,074 | 0 |
| merkle:15 → query:15 | 38,756 | 38,756 | 0 |
| query:15 → merkle:16 | 10,083 | 10,083 | 0 |
| merkle:16 → query:16 | 38,753 | 38,753 | 0 |
| query:16 → merkle:17 | 10,077 | 10,077 | 0 |
| merkle:17 → query:17 | 38,772 | 38,772 | 0 |
| query:17 → merkle:18 | 10,057 | 10,057 | 0 |
| merkle:18 → query:18 | 38,761 | 38,761 | 0 |
| query:18 → merkle:19 | 10,066 | 10,066 | 0 |
| merkle:19 → query:19 | 38,780 | 38,780 | 0 |
| query:19 → merkle:20 | 10,059 | 10,059 | 0 |
| merkle:20 → query:20 | 38,789 | 38,789 | 0 |
| query:20 → merkle:21 | 10,068 | 10,068 | 0 |
| merkle:21 → query:21 | 38,794 | 38,794 | 0 |
| query:21 → relation | 468,162 | 535,058 | **−66,896** |
| relation → final | 21,409 | 21,409 | 0 |

In this run, the full 66,896-CU stage-2 verifier reduction is in the `query:21` to `relation` checkpoint interval. All preceding logged intervals and the final interval match. This identifies a changed checkpoint window, not an isolated source-expression cost.

## Five fixture outcomes

Every shared-point run reused the same proof and public bytes as the corresponding h2 run. Stage-1 CU and serialized sizes match case by case. Terminal serialized sizes also match. Deltas are shared-point minus h2.

| Case | Proof SHA-256 | Public ASF8 SHA-256 | Stage 1 CU (shared / h2) | Stage 1 bytes (both) | Terminal CU (shared / h2) | Terminal delta | Terminal bytes (both) |
|---|---|---|---:|---:|---:|---:|---:|
| transfer, 13 pairs | `86d4212e675b36ebd556ca2b08b1b5e554cae15e77dfcd74c93a6f419129ed7c` | `f6bcd49446f1077d2c5ed4be940e91f0be444efc5ae83024ec0700b8c205c331` | 1,392,386 / 1,392,386 | 295 | 1,236,579 / 1,303,475 | **−66,896** | 879 |
| transfer, 255 pairs | `3d68309b72bf61f0cd36e02b49b4c7d3f8377df81dd7c9b24a25e44ba722908e` | `e201be4a028d74258c5344e7395bfabf7568af4ee7df0ec0c7b695f02fbacb15` | 1,392,164 / 1,392,164 | 295 | 1,302,702 / 1,369,686 | **−66,984** | 912 |
| withdrawal, 255 pairs | `dd83a7260a3a619cbe712ec591574ac625c0a38980c4c81ff6d3b26f8e13b853` | `7c2c27e135fa537776fad1457047f6c86ec351d64a8f0c6053674d2c2631200a` | 1,390,833 / 1,390,833 | 295 | 1,318,905 / 1,385,823 | **−66,918** | 1,077 |
| transfer, 1,023 pairs | `8569435667420b36a980493477f8fef7ef47e7351122647cf3747054079d4d62` | `72f067d263af326b017284579f30e3da7c843c6cbb29f1c6df94c8afbb1f2172` | 1,392,237 / 1,392,237 | 295 | 1,299,650 / 1,366,505 | **−66,855** | 912 |
| withdrawal, 1,023 pairs | `7bab9c8b102e6527118c589c984ef2b575bb046f18eaab4dc9c2926ec27d36f2` | `456bcde525f9e6947d9fc326daf3c3e01c8871cc4bf3d9fae6ab816980cb8f48` | 1,390,915 / 1,390,915 | 295 | 1,315,691 / 1,382,595 | **−66,904** | 1,077 |

The 13-pair transaction sizes and CU values come from the two exact `evidence.json` records above. The four larger shared-point records are `shared-point-contraction-v152-20261015/results/{transfer,withdrawal}-{255,1023}-evidence.json`; h2 records and matching original proof/public fixtures are in the [large-case bundle](evidence/wide-parser-unrolled-large-cases-20261015/large-cases-manifest.json). All five are local acceptance measurements on fixed fixtures and these two candidate ELFs.

The earlier [shared-point differential](evidence/shared-point-contraction-differential-20261015/README.md) used an explicit-scale manual case whose factors accidentally zeroed both scales. Its raw evidence remains unchanged. The corrected 72-case differential, including assertions for nonzero unequal `1/16` and `6/16` scales, is recorded separately in [the scale-fix bundle](evidence/shared-point-contraction-differential-scale-fix-20261015/README.md).
