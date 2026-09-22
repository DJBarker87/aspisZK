# Budget: a constraint, NOT a forecast

Measured pinned baseline: 3,279,621 CU, complete primary at the diagnostic cap.
It reaches 1,083,742 CU at prepare-end, before the query schedule/openings.
Both redundant reference costs were removed already. Merely deleting the
entire 1,265,198-CU ordinary/G terminal hypothetically leaves over 2M.

A possible allocation for a <1M objective is:

| Region | Current source interval sum | Engineering ceiling |
|---|---:|---:|
| Semantic + preparation | 1,043,765 | 300,000 |
| Points + records + authentication/post-auth | 738,614 | 300,000 |
| Query/tail + ordinary + G finish | 1,437,292 | 330,000 |
| Other, including query schedule and parsing | 59,950 | 50,000 |
| Total | 3,279,621 | 980,000 |

**These ceilings are not predicted achieved costs.** They show how demanding
the target is. The local arithmetic tests establish equality, not that every
ceiling is feasible. The whole-dot, semantic and prepared-opening experiments
must be measured separately and then composed on the same proof bytes.

Do not add claimed savings from overlapping experiments. Do not subtract a
reference pass from a primary-only baseline. Do not equate a host run time,
logical multiply count or small-field experiment to Solana CU.

If the lower-level exact variants still miss these limits, the present work
has not established a route under 1M. Any subsequent protocol redesign needs
its own concrete cost model and security analysis; 'recursion/GKR will fix it'
is not a measured solution, particularly if its public-input or wiring
polynomial evaluation simply recreates the same expensive work.
