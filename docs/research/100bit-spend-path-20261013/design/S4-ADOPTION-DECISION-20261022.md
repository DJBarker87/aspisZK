# S4 source adoption decision — 22 October 2026

The user explicitly authorized S4 PR #10 if needed, then stated “add up to 12k cu is ok”. Adopt the three-file candidate at PR head `5b23a95e6386a02fe12540403aa46067ee167c0d` as the next research source target. This supersedes the stage1-at-most-B1 condition in LEAD-FREEZE-20261020 only for this change, allowing up to 12,000 additional CU per transaction relative to the preceding frozen implementation. The configured 1,400,000 CU limit, split10, compact proof format, cryptographic parameters and 100-bit per-attempt target remain unchanged. This is source adoption, not deployment or proof closure.

## Retained measurements

Candidate artifact: `40dc75742430dd198bd51d519aa5a41bad4a45e8f173ccbd51c6d5be344ac3f0`.
Candidate counts come from `evidence/s4-combined-standing-retained-v2-20261021/receipts/work/runs/cu-*/evidence.json`. Baseline counts come from repository-root `lean-candidates/s4-const-generic-slot-candidate-v1-20261022/results/baseline/cu.json`, frozen revision b2727acd3abf79315d18b754a260f58f4b1c6326. That packet's const-generic candidate is NOT the adopted candidate; only its retained baseline counts are reused.

| Fixture | Stage 1 CU | Settlement CU | Stage 1 increase | Settlement increase |
|---|---:|---:|---:|---:|
| transfer-1023 | 1,204,226 | 1,179,790 | 10,798 | 10,484 |
| transfer-13 | 1,207,994 | 1,149,016 | 10,817 | 10,498 |
| transfer-255 | 1,210,100 | 1,180,061 | 10,814 | 10,503 |
| withdrawal-1023 | 1,205,984 | 1,186,828 | 10,806 | 10,487 |
| withdrawal-13 | 1,204,366 | 1,159,293 | 10,797 | 10,477 |
| withdrawal-255 | 1,204,498 | 1,189,265 | 10,799 | 10,496 |

These finite fixture comparisons are not analytical all-input bounds. Byte-identical proof/public inputs between the baseline and standing run have not been newly established here. The separate retained full OS-mask same-input control measured increases of 10,817 / 10,499 CU. Historical B1 gate failures remain recorded, not rewritten as passes.

## Validation reused and affected work

The standing packet checker passed: 30 native commands, six accepted fixtures, strict-stack and mutation gates, artifact/text identity. The current-overlay optimized native and SBF receipts both exited zero; the rebuilt verifier has the same retained artifact hash. No unchanged full regression was rerun. The current research changes since the review base touch simulator source only within the verifier crate, not these three adopted bodies. GitHub parameter and Poseidon bindings passed; formal build checks were cancelled, not passed. A final coherent formal replay remains required.

Adopted file hashes: fast_dots.rs `53fa714e84ded64b844061f4d1b66ad20ee1ba48c3873a73970f80ede8a0b602`; fast_pairing.rs `2cb96261cecfd766b5e1b45a585b74c5f59c20c6be4f41e806239e2786ca7313`; weights.rs `28b558ffa9f5b004188c7f50b1597fe681186f54fb4d52a3bd125df4f2481137`.

Reuse the proved generic indexed early-powers body for WideExact powers, including S9 N=4, rather than completing the superseded original from_fn adapter. QM31 kpowers and the helper terms from_fn remain separate boundaries. Regenerate the affected cone inventory and reconcile S1/S3/S4/S5/S9 and S8 caller pins; retain old pins as historical. No historical proof is silently reassigned to changed source. Final artifact/deployment pins, source/caller composition and the implementation-linked soundness theorem remain open. Target not yet established.
