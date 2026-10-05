# R837 active joint polynomial entry degree

For arbitrary field coefficients `half` and `quarter`, the R745 active-row branch satisfies `totalDegree ≤ 5` for every `d : Fin 255`, `s : Fin 3`, and active row `j : J`. The proof bounds `polynomialABC` by degree 2, treats source-derived `sourceBasisConstants` as coefficient-ring constants, bounds `pAlpha^(s.val+1)` by degree at most 3 using `s.val < 3`, and composes the finite three-term sum using the standard MvPolynomial degree inequalities. It does not expand the source basis or gather definitions.

Exact target `AspisV8R19/R837ActiveJointEntryDegree.lean`, source SHA256 `a4e4903fea56aee67df12836afcbb0ca5a3bf95bf7d9e162215844ffb383b5d2`. Green run `1791161434744724000-7dafbcd6e9d9`: exit 0, wall 1.74 s, peak Lean RSS 3,304,468 KiB, swap 0, Lean `-j1 -M4500`, cgroup MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, TasksMax=128. Full `#print axioms`: `polynomialABC_totalDegree_le` and `active_polynomialEntry_totalDegree_le` each depend on `[propext, Classical.choice, Quot.sound]`.

This proves only the active-row component of R834's uniform premise. The point and coefficient observation rows remain to be bounded before the premise can be discharged globally. No probability or security conclusion follows.
