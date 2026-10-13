# SamplerWordPass Lean evidence

- Target: `R1SamplerWordPass`
- Source: `docs/research/100bit-spend-path-20261013/lean/SamplerWordPass.lean`
- Source SHA-256: `16f37454a6d5e3672ee0f3a5c6c195926c3d9e64c4d7d423b79d1eabd87d6b11`
- Source revision: `0dbaf0c8d576a8da71e031b89cef2c9083c67cca` (worktree was already dirty; source hash identifies the compiled content)
- Remote workspace: `/home/dombarker/project-offloads/aspis-r1-concrete-decoder-20261013`
- Remote command: `./compile-one.sh R1SamplerWordPass h`
- Final result: exit status 0, wall time 1.10 s, peak RSS 1,683,696 KiB, swap 0.
- Cgroup: `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`, `TasksMax=128`; Lean threshold 5,000 MB.
- Runner SHA-256: `e567477ba2e054186b33f35b3dbf55a8a9c4399cd3baade5b5d145c1912dd901`.
- Environment manifest SHA-256: `d2f7294550dbdd9aa1cab186f25809c1a8b5a84d2fef74e3b3234052ced16c12`.
- Imported `R1SamplerWord.lean` SHA-256: `8206a4a664485894d4e3aff5443acfcff389445fb4e4c341269a9fd2aa440598`; imported object SHA-256: `dac76bc33208451899c68118b48617173993297d17c8ed5035b82388957597e6`.
- Imported `R1SamplerPass.lean` SHA-256: `631e025882495fcc5b2a402b9b002edc594080269c37553fd165499e61b9e0dd`; imported object SHA-256: `9de702ecb239e72703f060d5a336583c79e48e8445568f71d505b202fec6f269`.
- Archived `R1SamplerWordPass.olean` SHA-256: `7cb5c31ea28fe35a7380fd2bb0d9369119bb0d2138dec893396faebce08ba1ff`.

The final compiler output records `#print axioms` for `uint32_to_uint64_toNat`, `foldl_numeral`, `numeral_cons`, `machineProcess_length`, and `machineProcess_correct`. None reports `sorryAx`.

All focused attempts `a` through `h` have their receipt, compiler log, `/usr/bin/time -v` log, and source hash archived here. Attempt `h` compiled the final source with the axiom audit.
