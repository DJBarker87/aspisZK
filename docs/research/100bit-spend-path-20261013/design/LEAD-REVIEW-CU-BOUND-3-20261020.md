# Lead review: CU bound on the adopted format (2026-10-20)

Reviewed: cx-cu-bound3 (ebe1a2212), `evidence/cu-bound3-20261020/REPORT.md`,
method `PREREG-CU-UPPER-BOUND-2-20261019.md` unchanged, target the adopted
pins (verifier 8cf8d84e…, Pool 121f3e29…), reproduced exactly.

## Verdict: PASS over the admitted inputs

| Kind | B_stage1 | B_settlement | swept max stage 1 / settlement |
|---|---:|---:|---:|
| Transfer | 1,292,965 | 1,265,783 | 1,202,054 / 1,173,996 |
| Withdrawal | 1,292,314 | 1,278,858 | 1,200,657 / 1,183,771 |

752 accepted runs (300 random per kind), zero bound violations; 16,851
executed branches classified, zero unclassified, zero unexplained phase
variation; X-WEIGHTS-S2 executable check passed; bit-reversed query sets
attain the 914-node multiproof worst case.

The worker reports INCOMPLETE on the literal step-1 list, because the
adopted verifier rejects stage-1 split [3,11] for both kinds; only [3,10] is
admitted. A rejected input is outside (T)'s scope and outside the bound, so
coverage over admitted variants is complete. Ruling: PASS. The shrinking of
the admitted route set from {[3,10],[3,11]} to {[3,10]} is a behaviour change
of the adoption and is recorded here; it is acceptable (one split suffices)
and removes the +40.5k split-11 term of the first method.

## Margin

Stage 1 is 7,035 CU under 1,300,000 on the analytical bound (the swept
maximum is 98k under). Every verifier change re-runs this bound; the stage-2
refactor (0622ad3f…) and the deployment-id data constants have already
superseded this ELF, so the final bound is to be run once on the combined
freeze, with the harness and rules of this run.
