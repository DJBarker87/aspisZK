# Lead review: worst-case CU bound, second method (2026-10-19)

Reviewed: worker commit 11fa7c902 (branch `codex/r1-cu-bound2-20261019`),
evidence `evidence/cu-bound2-20261019/`. Criteria:
`design/PREREG-CU-UPPER-BOUND-2-20261019.md` (cf1828114), unchanged.

## Verdict: PASS, as pre-registered

| | Transfer | Withdrawal |
|---|---:|---:|
| B_stage1 (analytical) | 1,283,656 | 1,282,782 |
| B_settlement (analytical) | 1,199,817 | 1,212,803 |
| Worst measured variant, stage 1 / settlement | 1,239,122 / 1,165,208 | 1,237,750 / 1,174,590 |
| Swept max, stage 1 / settlement (886 accepted runs) | 1,239,160 / 1,165,208 | 1,237,750 / 1,174,664 |

Every executed branch is classified (16,662, including the 69 Pool
`call_once` sites); 0 of 196 varying verifier phases and 0 of 80 varying Pool
functions unexplained; no swept value exceeds its variant's bound. Pins:
Pool 121f3e29… (= B1); verifier 4421aafd…, `.text`/`.rodata` identical to
a70f30bd… (39 bytes of panic line numbers in `.data.rel.ro` shifted by the
cfg(prover) enum variants). Controls reproduce B1 exactly. Traces (20 GB)
deleted; no binaries committed.

**G_R1.1 (≤ 1.3M per transaction) is met by an argument with executable
checks**, under the assumptions below. Stage-1 margin is thin: 16.3k
(transfer) and 17.2k (withdrawal); settlement margin 100k / 87k. Any
verifier change that adds work to stage 1 must re-run this bound.

## Lead check of the rules (`harness/make_rules.py`)

The 28 exclusions are of four kinds, all acceptable: variant constants (kind,
history mode, prefund, proof variant S2, route), which are sound because B is
computed per variant and maximised; arms that only reject; fixed-length Vec
growth with cited capacities; and stored-bump/hint fallbacks that can only
reject. The 27 loop caps cite constant trip counts or source bounds.
One exclusion rests on a data fact rather than a constant, and is flagged for
an executable check before release: **X-WEIGHTS-S2** ("statement point rows
0 and 2 differ only at coordinates 6 and 7", state_only_prefix.rs:600-614).

## Assumptions the bound rests on (worker REPORT §7)

1. A call inside a counted never-taken arm is costed at the callee's
   observed maximum, not a proven one (same as the first method).
2. Positional decision classes are empirical (identical across 4–26 traced
   runs per variant).
3. Eight loop caps use the traced per-entry maximum; seven loops have
   constant trip counts; the eighth (query-scan `contains`) is argued from
   every accepted run passing accepted_len 0–21.
4. Source lines come from a line-tables build whose `.text` differs; lines
   are attached only where function bytes match.
5. Transcript-driven sites (value branches, circle fallback, duplicate query
   draws) cannot be targeted without breaking Fiat-Shamir and are covered by
   residuals only.

## Follow-ups

- Executable check for X-WEIGHTS-S2.
- Bound re-run triggered by any change to verifier stage-1 code.
