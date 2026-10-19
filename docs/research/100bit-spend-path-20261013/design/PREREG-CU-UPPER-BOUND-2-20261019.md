# Pre-registration: worst-case CU upper bound, second method (2026-10-19)

Written by the lead before any work starts. Criteria may not change after
results are seen. This is a **second method**, not a revision of
`PREREG-CU-UPPER-BOUND-20261019.md`; that method's FAIL
(`LEAD-REVIEW-CU-BOUND-20261019.md`) stands as recorded.

## Target

`research` at the job's base commit, after Pool B1
(`LEAD-REVIEW-POOL-B1-20261019.md`). The verifier is rebuilt from the base
source (it changed after bee5825f0) and the Pool from the base source; the job
pins both ELF SHAs and confirms the six control replays against freshly built
fixtures before anything else. Features as in the first method. Two
transactions: stage 1 and Pool settlement, for transfer and withdrawal.

## Method (fixed)

1. **Variants measured, not added.** Every admitted discrete variant is
   measured directly at its worst point: stage-1 split [3,10] and [3,11];
   transfer and withdrawal; rollover and no rollover; history modes; pair
   position at 0, at 2^20−1 and at the positions the first method's traces
   identified as most expensive. B is computed per variant and the maximum
   over variants is taken.
2. **Per-site residual, not per-site total.** For every data-dependent site
   (first method's `sites.json`, re-derived for the rebuilt ELFs), the extra
   counted is (maximum cost of the site over all inputs) minus (cost of the
   site in the measured worst input of that variant), using per-site traced
   counts. A site already at its worst in the measured input adds 0.
3. **Mutual exclusion only with a code-cited reason.** Arms are combined by
   max instead of sum only where the code shows they cannot both execute in
   one accepted run (same condition, a route or kind constant, or
   control-flow exclusivity in the ELF). Otherwise they are summed.
4. **Never-taken arms (first method's R3).** Each is either shown
   unreachable for accepted inputs with a code citation, or counted at full
   cost.
5. **Coverage.** Every executed conditional branch in both ELFs is
   classified, including the 69 Pool sites in the `call_once` closure left
   unclassified by the first method. Any unclassified site makes the result
   INCOMPLETE.
6. **Consistency.** With `cu-profiling`, every verifier phase's variation is
   attributed to listed sites (0 unexplained). For the Pool, function-level
   attribution from traces, 0 unexplained.
7. **Sweep.** At least 256 valid accepted transactions per kind (random
   witnesses, masks, tree positions across 0..2^20−1, both stage-1 splits,
   rollover), plus targeted inputs per site. No sweep value may exceed its
   variant's B; one that does voids the bound.

## Acceptance

- PASS: B_stage1 ≤ 1,300,000 and B_settlement ≤ 1,300,000 for each kind,
  steps 1–7 complete, sweep maximum ≤ B.
- FAIL: either bound > 1,300,000. Report the dominant sites; no redesign.
- INCOMPLETE: any unclassified site, or any site whose maximum lacks a
  code-cited cap.

## Labels

An argument with executable checks, not a formal proof. Rejected
transactions are out of scope. Measured, analytical and swept figures are
labelled separately.
