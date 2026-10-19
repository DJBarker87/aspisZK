# Lead review: worst-case CU bound (pre-registered), 2026-10-19

Reviewed: branch `codex/r1-cu-bound-20261019` (c679871c7, 7d77b283c,
342170cd4), evidence `evidence/cu-bound-20261019/`. Criteria:
`design/PREREG-CU-UPPER-BOUND-20261019.md` (bee5825f0).

## Verdict: FAIL, as pre-registered

| | Transfer | Withdrawal |
|---|---:|---:|
| B_stage1 (analytical) | 1,357,041 | 1,358,920 |
| B_settlement (analytical) | 6,204,876 | 6,986,751 |
| Swept max stage 1 (658 accepted runs) | 1,239,161 | 1,237,878 |
| Swept max settlement | 1,231,724 | 1,245,323 |

Every site has a code-cited cap, so the verdict is not INCOMPLETE. The target
ELFs were rebuilt byte-identically (verifier a70f30bd…, Pool b33302fd…); the
six control replays reproduce the fixture CU exactly. No sweep run exceeded
its bound.

## Findings the fixtures had hidden

1. **Pool PDA searches.** `programs/aspis-pool` still calls
   `find_program_address` (21 sites; 11–12 calls per transfer settlement,
   13–14 per withdrawal). Agave 4.2.1 charges 1,500 CU per bump attempt, up
   to 255 attempts. G_R1.8's stored canonical bumps were applied to the R1
   verifier program, not to the Pool. Seeds that are constant per deployment
   (state, vault, registry, pair state) cost a fixed, already-measured amount;
   the worst case comes from seeds that vary per transaction (nullifier,
   history page, pair-forest page, prepared-settlement sequence).
   A ground nullifier needing 19 attempts measured 1,231,724 / 1,245,323.
2. **Stage-1 split [3,11]** is admitted (`pool_route.rs:4`) but no fixture
   used it; it adds about 40.5k CU to stage 1.
3. **Pair positions** are admitted up to 2^20−1 (1023 was a driver limit);
   CU is not monotone in position; the cap was measured.

## Reading of the bound

The pre-registered method adds each site's worst arm independently and adds
it on top of the worst fixture, which double-counts what the fixture already
paid and combines arms that may be mutually exclusive. So the analytical
figures are upper bounds, possibly loose; the FAIL stands because the
criterion was fixed in advance. Without the bump searches, B_settlement is
still 1.63M (Pool page-mode branches and loops), against a swept maximum of
1.25M; without the conservative never-taken arms (R3), B_stage1 is 1.307M.

## Decisions needed (user)

- **Pool bumps (blocking any PASS).** The variable-seed PDAs, nullifier above
  all, need either a canonical-bump design without a search, or an explicit
  probabilistic tail rule. For a nullifier the bump must stay canonical, or a
  second account could be created for the same nullifier.
- **A second, tighter bound** under a new pre-registration (subtract
  fixture-included cost, handle mutually exclusive arms), labelled as a second
  method, not a revision of this one.

## Unresolved

69 Pool branch sites in one `call_once` closure (1.2–3% of Pool instructions)
are unclassified. No redesign was done in this job.
