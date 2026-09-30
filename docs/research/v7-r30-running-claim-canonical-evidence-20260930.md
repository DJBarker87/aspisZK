# V7 R30 source running-claim canonicality

Source predecessor `cc1830517`, plus working source hashes below. Each focused
target used pinned Lean 4.32 dependencies and its own remote scope with
MemoryHigh=7G, MemoryMax=8G, MemorySwapMax=0. One scope at a time; swaps were
zero for every check. No complete manifest or runtime regression was run.

The dispatch now retains the exact first-row read, compact-polynomial decode,
and first Horner-evaluation equations. These are populated from the same
successful source branch, not added as free canonicality assumptions. The
running claim before insertion follows from the initial claim, two source
circle steps, canonical relation decoding, and the source evaluator. The
post-insertion claim follows from the literal callback's canonical query
values, shifted rho powers, sixteen-input dot product, and source checked add.

| Focused target | Exit | Wall s | Peak KiB |
| --- | --- | --- | --- |
| V7CallerCurrentReleaseR30InitialPrechallengeDispatch | 0 | 11.55 | 7169568 |
| V7CallerCurrentReleaseR30InitialFoldSixSource | 0 | 4.58 | 7183460 |
| V7ProductionSnapshotObserverR30InitialFoldSource | 0 | 4.09 | 7162972 |
| V7CallerCurrentReleaseR30InitialFoldSixSemantics | 0 | 4.29 | 7179072 |
| V7ProductionSnapshotObserverR30InitialFoldSemantics | 0 | 4.42 | 7196984 |
| V7ProductionSnapshotObserverR30InitialFoldTail | 0 | 4.86 | 7207164 |
| V7ProductionSnapshotObserverR30CurrentTailCanonical | 0 | 4.55 | 7194808 |
| V7ProductionSnapshotObserverR30QueryFoldCanonical | 0 | 4.36 | 7147352 |
| V7ProductionSnapshotObserverR30RunningCanonical | 0 | 4.78 | 7202712 |

Changed-source SHA256:

- InitialPrechallengeDispatch: `10054fa4c6b711ca5603b135e6ac5272530ae975477474217fe320e682af1f2d`
- RunningCanonical: `1e6baa168024aff7a6e7372b46b743779aa50718c92442b8acfe71217b2c7435`

All printed source-extraction, callback, before-insertion, and after-insertion
theorems have only `propext`, `Classical.choice`, `Quot.sound`. The unchanged
dependent files were rebuilt specifically because the dispatch structure changed.

Failed focused preflights were import/environment or default-instance plumbing:
dispatch exit 1 at 0.78s/865060KiB (incomplete backend Mathlib root), then
5.64s/1614228KiB (missing R26 proof cache); running bridge exit 1 at
1.73s/2199756KiB (missing scale-loop cache), 4.92s/7123672KiB,
5.26s/7123292KiB, and 4.67s/7134516KiB (different default instances on bounded
list reads). The wrapper explicitly restores the pinned LEAN_PATH after
`lake env` and includes both existing R26 proof caches. Bounded reads now
eliminate defaults symbolically. No resource failure or raised cap occurred.

This discharges the previously missing `runningCanonical` premise. The final
terminal composition and frozen replay remain to be performed; this is not a
standalone claim of complete cryptographic soundness.
