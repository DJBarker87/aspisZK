# Lead review: final CU bound on the frozen R1 verifier (2026-10-20)

Reviewed: cx-cu-bound4 (eaafab389), `evidence/cu-bound4-20261020/REPORT.md`;
method `PREREG-CU-UPPER-BOUND-2-20261019.md` unchanged, as applied in
`LEAD-REVIEW-CU-BOUND-3-20261020.md`; target the frozen verifier
(`LEAD-FREEZE-20261020.md`: default ELF dfc2a91a…, Pool 121f3e29…),
reproduced from source.

## Verdict: PASS over the admitted inputs (stage-1 split [3,10])

| Kind | B_stage1 | B_settlement |
|---|---:|---:|
| Transfer | 1,294,560 | 1,269,370 |
| Withdrawal | 1,293,942 | 1,282,451 |

Minimum margin 5,440 CU (transfer stage 1). 746 accepted corpus replays,
16,948 executed branches classified (zero unclassified), zero unexplained
profile variation, zero sweep violations. Traces (15.4 GB) deleted after
hashing.

G_R1.1 (≤ 1.3M per transaction) holds for the frozen R1 verifier by the
pre-registered argument with executable checks, under the method's stated
assumptions (first-method REPORT §7 as carried into the second method). It
is not a formal proof. The stage-1 margin is 5.4k: the next freeze (which
folds the tx1_finish refactor) re-runs this bound, and any source change
that adds stage-1 work is to be measured against that margin before
adoption.
