# Const-generic slot candidate: bounded gate result

This is an isolated performance experiment, not an adopted source change. It specializes the already-gated `four_dots_one` helper over `const SLOT` and instantiates slots 0–3. The helper body and arithmetic/parser order are unchanged; no `inline(always)` annotation is present. The variant is one changed Rust blob relative to the three-source candidate base.

The optimized native `dots_equivalence` test passed (2 tests), and all six optimized SBF fixture executions preserved checkpoint-tail and return-data hashes. The strict stack audit passed. **The candidate fails strict B1 on all six fixtures**, so the optimization probe stopped here; there was no follow-up sweep, source adoption, freeze change, PR, or deployment.

| Fixture | Stage 1 actual / runner-baseline delta / B1 | Stage 1 | Settlement actual / runner-baseline delta / B1+10k | Settlement | Output hashes |
|---|---:|:---:|---:|:---:|:---:|
| cu-transfer-1023 | 1197066 / +3638 / 1199687 | PASS | 1171198 / +1892 / 1170974 | FAIL | tail + return data match |
| cu-transfer-13 | 1200834 / +3657 / 1199648 | FAIL | 1140424 / +1906 / 1139757 | FAIL | tail + return data match |
| cu-transfer-255 | 1202940 / +3654 / 1199567 | FAIL | 1171469 / +1911 / 1171066 | FAIL | tail + return data match |
| cu-withdrawal-1023 | 1198824 / +3646 / 1198386 | FAIL | 1178236 / +1895 / 1180263 | PASS | tail + return data match |
| cu-withdrawal-13 | 1197206 / +3637 / 1198225 | PASS | 1150701 / +1885 / 1148950 | FAIL | tail + return data match |
| cu-withdrawal-255 | 1197338 / +3639 / 1198264 | PASS | 1180673 / +1904 / 1180523 | FAIL | tail + return data match |


The combined gate fails on 6/6 fixtures. Stage-1 fails on transfer-13, transfer-255, and withdrawal-1023; settlement fails on transfer-1023, transfer-13, transfer-255, withdrawal-13, and withdrawal-255. Withdrawal-1023 passes settlement but fails stage 1. Candidate SBF ELF SHA-256 is `409da0d0c86383929b60c6f548c522bb26fc6a0fde5937f3174dcdcd703cf512` (1,542,424 bytes). Baseline artifact SHA-256 is `dfc2a91ab24e1ec4f57debd8f124cb4f6a3c38ba2662b7318e2e4f3b4acdde34`.

Build and gate receipts, raw fixture outputs, strict-stack report, source manifests, and per-phase collector admissions are in `results/`. The packet contains no compiled binaries. All heavy phases ran on NUC in separately admitted scopes with `MemorySwapMax=0`. Admission snapshots are retained verbatim. The source baseline was review commit `5b23a95e6386a02fe12540403aa46067ee167c0d`; its admitted three-source candidate files were applied to the pinned `b2727acd3abf79315d18b754a260f58f4b1c6326` source tree for the SBF build. Within that candidate base, only `fast_dots.rs` differs for this experiment.

To check the source patch, run `python3 check_candidate.py`. To validate the retained result and file hashes, run `python3 check_packet.py` from this directory. This packet does not claim adoption readiness or waive B1.

The delta columns compare against the runner baseline artifact, while the B1 columns are the separately frozen acceptance thresholds. The inline-only probe at `85c4adeb` is historical evidence and is not the source of this no-inline candidate.
