# Current goal: candidate 12, transaction-local rho residues

User direction: prove the optimizations with the largest measured CU savings
first. Gamma reuse is paused, not completed. Candidate 6 remains the one closed
replacement under the existing reference source/runtime assumptions.

Descending remaining combined incremental saving (six measured fixtures):

| Candidate | Stage 1 | Settlement | Combined range |
|---|---:|---:|---:|
| 12 rho residues | 42,693–42,746 | 51,250–51,356 | 93,943–94,102 |
| 4 delayed base dots | 28,221–28,252 | 33,880–33,932 | 62,101–62,184 |
| 3 fixed S2 groups | 0 | 40,517–40,520 | 40,517–40,520 |
| 1 gamma reuse | 34,201–34,243 | 0 | 34,201–34,243 |
| 14 Libra factorization | 0 | 33,363–33,427 | 33,363–33,427 |
| 2 profiling | 10,992 | 13,201 | 24,193 |
| 5 canonical dots | 11,273–11,286 | 11,617–11,630 | 22,890–22,916 |
| 10 fixed prefix | 5,620 | 6,744 | 12,364 |
| 7 geometry reuse | 780–791 | 947–957 | 1,727–1,748 |

The combined ranges above sum independent minima/maxima, so are conservative
envelopes, not assertions that both extrema occur in the same fixture.
Source: ../cu-savings-20261019/FINAL-REPORT.md.

Completion requires the exact old/new candidate-12 source bridge, canonical
initialization and sufficient-resource allocation admission, all-row query
invariants and checked counter increment, actual canonical reference field
update, finish/checkpoint and caller composition, all covered success/error/
divergence paths and observations under precisely the existing reference
boundary. No unproved candidate-equivalence premise may remain. Focused Lean
checks and #print axioms, pinned source/tool/cache receipts and a pushed proof
commit are required. Production Rust and the root checkout remain untouched.

The goal is not complete merely because the push/value/finish components pass.
No generic compiler expansion is authorized by this goal.
