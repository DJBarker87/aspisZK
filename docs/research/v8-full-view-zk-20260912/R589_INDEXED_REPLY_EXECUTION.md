# R589: indexed reply execution

R589 proves generic full-view chronological indexed-reply execution for program bind and finite-tape evaluation. It then specializes this machinery to deterministic block-cursor global-word reads and one bounded-rejection limb of the R584 block sampler. The specialization preserves the cursor and next-block counter across read and refill paths.

## Verification

- Canonical source: `lean/AspisV8R19/R589IndexedReplyExecution.lean`
- Original draft: `.r21-scratch/R589IndexedReplyExecution.UNVERIFIED.lean`
- Canonical/draft SHA256: `4f1a8a42443ac1fd3bdc00bcfdb0bbc8f4b2cd9d416aecfd11214d974abe6c6d` (byte-identical)
- Source revision: `b3b076cfe7c5d099a63b6ac1ecec2a11ecb59e24`
- Final canonical module-path receipt: `1791087962201787000`; exit 0; wall 1.77 s; Lean-child peak RSS 3,276,248 KiB; swap 0.
- Resources: `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`; Lean `-j1 -M4500`.
- Seven complete final `#print axioms` reports are retained. `indexedResult_done` has none; the remaining declarations use only subsets of `[propext, Classical.choice, Quot.sound]`.

All four requested attempt triples, exact direct import sources, runner, explicit publish paths, and recursive SHA manifest are in `evidence/r589-indexed-reply-execution/`. No focused job was rerun for this promotion.

## Boundary

R589 is generic full-view chronological reply-counter bind and `evalTape` equality, plus deterministic block-cursor global-word read/refill and one-limb bounded-rejection mapping. It does not prove the source independent law, complete four-limb coupling, tape mass, or a shared-oracle comparison.

The first remaining work is generic all-limbs-budget block-program coupling and the initial challenge, then R587’s `Within 4` with R579/R578 mass, followed by the actual shared-oracle comparison.
