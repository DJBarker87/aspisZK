# SamplerRanking Lean evidence

- Target: `R1SamplerRanking`
- Source: `docs/research/100bit-spend-path-20261013/lean/SamplerRanking.lean`
- Source SHA-256: `f41de78e7b64f737df7b86346f2f39972a0165fdf275ced4957b6a6372395b4b`
- Source revision: `a7ff42dc8068119ba1aea4e7bda471a01177b5be` (worktree was already dirty; this source hash identifies the compiled content)
- Remote workspace: `/home/dombarker/project-offloads/aspis-r1-concrete-decoder-20261013`
- Remote command: `./compile-one.sh R1SamplerRanking f`
- Runner SHA-256: `e567477ba2e054186b33f35b3dbf55a8a9c4399cd3baade5b5d145c1912dd901`
- Environment manifest SHA-256: `d2f7294550dbdd9aa1cab186f25809c1a8b5a84d2fef74e3b3234052ced16c12`
- Final result: exit status 0, wall time 0.74 s, peak RSS 1,689,796 KiB, swap 0.
- Cgroup: `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`, `TasksMax=128`; Lean threshold 5,000 MB.
- Archived Lean object SHA-256: `e430e5f0dab6e02da7195f6d41a88141bd9af9e3060b6b2a7f54d7edee9e7922`.

The final compiler output records these `#print axioms` results:

```text
AspisR1.SamplerRanking.digitsRank_symm_apply_val: [propext, Classical.choice, Quot.sound]
AspisR1.SamplerRanking.digitsRank_value: [propext, Classical.choice, Quot.sound]
AspisR1.SamplerRanking.canonicalDigits_eq_rank_symm: [propext, Classical.choice, Quot.sound]
```

Every attempt `a` through `f` has its receipt, compiler log, `/usr/bin/time -v` log, and source hash archived here. Attempts `a` through `d` capture the initial import and proof iterations; attempt `e` first compiled successfully, and `f` compiled the final source with the axiom audit.
