# R588 normalized-core product-domain bound

R588 proves a finite-domain Schwartz–Zippel bound for the normalized-core determinant over three independent coordinates of `QM31Exact`. For any fixed `half`, coordinate domains `S : Fin 3 → Finset QM31Exact`, and integer `m > 0` with every domain size at least `m`, the fraction of assignments in `Fintype.piFinset S` where the determinant vanishes is at most `1355 / m`.

The proof applies the existing Schwartz–Zippel support-sum theorem to the determinant polynomial. Its nonzeroness and total-degree bound (`≤ 1355`) come from R585. No premise says that the selected transcript sampler realizes a product distribution on these domains. This result does not establish adaptive circle-parameter conditioning, actual challenge-law correspondence, query-root repair, an overall security-bit bound, or privacy/security closure.

The precise next missing argument is the actual selected verifier’s joint accepted-challenge law under its adaptive transcript, retry, and stopping behavior, together with the low-query repair needed to apply this determinant bound to the source’s full G observation map.

## Verification record

- Canonical target: `AspisV8R19/R588NormalizedCoreDomainBound.lean`.
- Exact source SHA256: `778c2f74195df38881b25a22e3497a7b438553d5f92017dc0f6893e3274de4b3`.
- Source revision at focused compilation: `b3b076cfe7c5d099a63b6ac1ecec2a11ecb59e24`.
- Scratch focused target `AspisV8R19/R588NormalizedCoreDomainBoundScratch.lean`: green, run `1791087742923329000`, exit 0, wall 1.98 s, peak RSS 3,789,528 KiB, swap 0.
- Canonical-path focused target: green, run `1791087806331144000`, exit 0, wall 2.01 s, peak RSS 3,789,012 KiB, swap 0.
- Both used the pinned Lean 4.32 cached workspace, `-j1 -M4500`, and a systemd user scope with `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`.
- Complete `#print axioms` output for both declarations:

  - `normalizedDet`: `[propext, Classical.choice, Quot.sound]`.
  - `normalizedDet_domain_fraction_bound`: `[propext, Classical.choice, Quot.sound]`.

The evidence directory contains all three scratch attempts, the canonical-path check, their exact source snapshots, logs, receipts, direct dependency snapshots, and checksums. The first failed attempt used an unqualified Mathlib theorem name; the second exposed tactic recursion depth in the copied proof route. The final source qualifies the theorem and sets `maxRecDepth` to 4096. No CU benchmark, broad regression, or source verifier was run.
