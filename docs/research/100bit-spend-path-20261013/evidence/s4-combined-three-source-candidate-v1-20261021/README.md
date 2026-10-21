# S4 combined three-source candidate V1

This is a reviewable, isolated source candidate over frozen baseline `b2727acd3abf79315d18b754a260f58f4b1c6326`, built from candidate base `85c4adeb66d0a641bcdf58cc470751e6d67ab8d0`. The only Rust source differences are the three files retained in `candidate-source/`, with exact SHA-256 pins in `source-pins.json` and a reproducible source patch in `candidate.patch`.

The candidate combines the V10 fixed-call `fast_dots` helper, the early-return indexed `weights::powers` loop, and four ordered comparisons in `Q::from_limbs`. Existing source-cut and Lean evidence is referenced below. Those are component-level results; they do not constitute one formal proof of the combined current caller, the Rust standard-library behavior, or the compiled SBF semantics.

## Validation

The optimized SBF artifact is SHA-256 `40dc75742430dd198bd51d519aa5a41bad4a45e8f173ccbd51c6d5be344ac3f0` (1,508,152 bytes). The isolated build succeeded in a fresh High=2 GiB / Max=4 GiB / Swap=0 scope. The six CU fixtures produced identical checkpoint-tail and return-data hashes to their frozen references, and strict-stack passed. The exact rows and receipts are in `six-fixture/gate-result.json` and `build/`.

The preregistered B1 item-1 criterion **fails on all six fixtures**. The stage-1 cost is 4,539–10,533 CU over B1. Settlement cost exceeds B1+10,000 by 6,565–10,343 CU. This is a failure even though the artifact is below 1.4 million CU and the observed outputs match. The exact per-fixture comparison is in [`b1-table.csv`](six-fixture/b1-table.csv), while `six-fixture/gate-result.json` also records candidate-minus-measured-baseline deltas. These are different comparisons and must not be conflated.

The 30-command standing suite completed with 30/30 exit status zero in its fresh High=2 GiB / Max=4 GiB / Swap=0 cgroup. Its command manifest, per-command stdout, timing and receipts are retained in `standing/` and `standing-result.json`. The suite passing does not override the six-fixture B1 failure.

## Component proof/source lineage

- V10 literal helper source-cut: [`s4-v10-literal-helper-source-cut-v1-20261021`](../s4-v10-literal-helper-source-cut-v1-20261021/README.md) proves all-Result equality between the copied literal emitted helper and its fixed-v6 model after named operation/carrier slots. It leaves Rust `array::from_fn`, standard-library installation, and frozen-source adoption open.
- V10 outer transport: [`s4-v10-literal-outer-transfer-root-v1-20261021`](../s4-v10-literal-outer-transfer-root-v1-20261021/README.md) transports the candidate literal outer body through the helper result. It does not close raw operation installation or the complete S4 source cone.
- Early-return powers: [`s1-early-return-powers-proved-candidate-20261020`](../../lean-candidates/s1-early-return-powers-proved-candidate-20261020/README.md) proves the isolated emitted candidate total and exact on canonical inputs. Its native differential suite is finite evidence, not a universal Rust standard-library theorem.
- Checked-Q candidate: [`s4-checked-q-all-unrolled-candidate-v1-20261021`](../../lean-candidates/s4-checked-q-all-unrolled-candidate-v1-20261021/README.md) records exhaustive predicate partitions, boundary tests and deterministic differential tests plus a Lean source-cut result for the candidate method. It does not prove equivalence of the frozen production method or Rust `Iterator::all` implementation.

## Status

Candidate only; not adopted and not a release freeze. Do not copy it into the frozen source or deploy it based on this packet. Adoption would require an explicit disposition of the B1 failure, new source/artifact repins and the remaining whole-cone source/runtime proof obligations. No production source, frozen artifact, or deployment was changed by this candidate validation.
