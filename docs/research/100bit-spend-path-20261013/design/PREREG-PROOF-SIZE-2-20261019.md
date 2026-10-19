# Pre-registration 2: adopting the compact binary-multiproof proof format (2026-10-19)

User decision after `LEAD-REVIEW-PROOF-SIZE-20261019.md`: a settlement CU
rise of the measured size is acceptable in exchange for the 57,607-byte
proof. This is a new pre-registration; the first test's NOT VIABLE verdict
under its own line stands as recorded.

## Decision

The compact binary-multiproof format (fixed length 57,607 bytes, the S3
candidate `compact-binary`) becomes the R1 proof format. The verifier source
freeze of the soundness gap map (step 0) is taken on it. Per
`proof-size-priority`, this is prioritised over new soundness and privacy
work on the eight-way format.

## Acceptance for the adopted build (fixed before measurement)

1. Settlement CU per fixture ≤ its B1 figure + 10,000; stage-1 CU per fixture
   ≤ its B1 figure.
2. The second-method worst-case bound (`PREREG-CU-UPPER-BOUND-2-20261019.md`,
   same method, same rules) re-run on the adopted ELFs gives B_stage1 ≤
   1,300,000 and B_settlement ≤ 1,300,000 for both kinds.
3. The P_R1 retrying prover path (D73/D74) produces proofs in the new format
   that verify on the adopted build (gate ≥ 8/8).
4. The shipped default build is the new format; the eight-way path is
   retained behind an audit-only feature for differential evidence, not
   selectable by a prover or program build.
5. Standing gates: codec 1,233, ordered trace, checkpoint tests, Pool suites,
   stack audit, mutation and double-spend tests, all pass on the adopted
   build.
6. Wallet upload chunk raised to the TxV1 maximum (3,767 bytes measured);
   upload count for a full spend ≤ 17 (16 proof + 1 statement).

PASS requires all six. Measured, analytical and swept figures are labelled
separately; the result is not a security claim until the obligations in
`PROOF-SIZE-OBLIGATIONS-20261019.md` close.
