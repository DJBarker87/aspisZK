# SamplerWord Lean evidence

- Target: `R1SamplerWord`
- Source: `docs/research/100bit-spend-path-20261013/lean/SamplerWord.lean`
- Source SHA-256: `8206a4a664485894d4e3aff5443acfcff389445fb4e4c341269a9fd2aa440598`
- Source revision: `0dbaf0c8d576a8da71e031b89cef2c9083c67cca` (worktree was already dirty; the source hash identifies the compiled content)
- Remote workspace: `/home/dombarker/project-offloads/aspis-r1-concrete-decoder-20261013`
- Remote command: `./compile-one.sh R1SamplerWord l`
- Final result: exit status 0, wall time 0.95 s, peak RSS 1,661,604 KiB, swap 0.
- Cgroup: `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`, `TasksMax=128`; Lean threshold 5,000 MB.
- Runner SHA-256: `e567477ba2e054186b33f35b3dbf55a8a9c4399cd3baade5b5d145c1912dd901`.
- Environment manifest SHA-256: `d2f7294550dbdd9aa1cab186f25809c1a8b5a84d2fef74e3b3234052ced16c12`.
- Imported `R1SamplerMachineBounds.lean` SHA-256: `cb1d5e53fa26c968d16d84f4011747842c41d6a05c24bece76319f00023f54cd`; imported object SHA-256: `c3e5cab22b2c70acd29d72ba5ad4ac964fb8cd5d1d26bff297973ac28b9c7bad`.
- Archived `R1SamplerWord.olean` SHA-256: `dac76bc33208451899c68118b48617173993297d17c8ed5035b82388957597e6`.

The final compiler output records `#print axioms` for all principal results: `packNat_of_lt`, `packNat`, `packNat_lt_two63`, `modelExpr_lt_two63`, `modelExpr_UInt64_roundtrip`, `machineWord_toNat`, `machineWord_lt_two63`, `machineStep_quotient_toNat`, and `machineStep_remainder_toNat`. Each reports `[propext, Classical.choice, Quot.sound]`; none reports `sorryAx`.

All focused attempts `a` through `l` have their receipt, compiler log, `/usr/bin/time -v` log, and source hash archived here. Attempt `l` compiled the final source with the axiom audit.
