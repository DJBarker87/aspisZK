# Lead review: J1.R13 report (checkpoint worker, 2026-10-19)

Merged from `codex/r1-checkpoint-recut-20261018` at 6feb295c2. Report:
`evidence/j1r13-artifact-20261019/checkpoint-report.json`. ELF SHA-256
`4e1fd78fbddb39cb9599de7694105547d8e86e7451f8b9f3e9626789036e8711` is the
pinned Decision 1h artifact.

## Rollover: the reported 255-pair failure is refuted

All four rollover cases pass under the 1.4M cap on this artifact:

| Fixture | Stage-1 tx CU | Pool settlement CU |
|---|---:|---:|
| Transfer 255 | 1,340,886 | 1,366,325 |
| Withdrawal 255 | 1,339,527 | 1,380,079 |
| Transfer 1023 | 1,340,971 | 1,363,282 |
| Withdrawal 1023 | 1,339,699 | 1,376,825 |

The earlier note of a 255-pair failure (v3b, live session) does not
reproduce on these fixtures with this ELF.

## G_R1.1: two transactions under 1.3M is not reachable by rebalancing

Worst case needs 119,606 CU of combined savings. Moving one query from
stage 1 to settlement would put settlement at an estimated 1.413–1.429M,
over the hard cap, so the split cannot move. Both transactions sit under
the 1.4M cap today with 60k (stage 1) and 20k (worst settlement) headroom.
The remaining routes are arithmetic optimisations and claim deferral,
costed in the report with unmeasured savings labelled as such. **The lead's
reading: the ≤1.3M-per-transaction target is a design target that the
current two-transaction R1 does not meet, and cannot meet by moving work
between the two transactions. Either the target is restated against the
1.4M cap with an explicit margin, or ~120k CU of arithmetic savings must be
found. This is a user decision.**

## Metadata harness: partial

One control and two mutations passed; then LiteSVM rejected the
executable-account setup with IncorrectProgramId before verifier entry, and
12 of 15 cases did not run. A driver-only repair is proposed and unapplied.
The R16ReadonlyMetadataProjection premise is therefore still without full
runtime backing.

## Hygiene for the unified build

All three "missing" sources exist in tracked evidence. The report proposes
canonical placement, import-only `R1X` alias forwarders for the X/R1X double
imports, and coherent current-split ownership for the three collisions, with
importers and hashes listed. These are the inputs for the soundness roots'
entry into the unified build (LOG D63.2).
