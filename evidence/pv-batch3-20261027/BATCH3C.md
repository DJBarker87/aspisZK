# Batch3c resume — D323 repair authorization

Entry 73a25b0b8bab8250accdbaac79d397fdf410a8ac, exact worktree and branch retained. Budget: 85 additional Lean attempts, zero Kani; focused IDs37916–37996, audit37997–37999. Rejected source0b048ee98d and counterexample retained; never adopted.

The authorized repair adds level20 to both fixed legacy path/append expansions, restoring POOL_V1_PAIR_PRIVATE_DIRECTIONS=21 and all127 links. The127-link check is unchanged. host_forest remains behind the prover feature (lib.rs1619); the frozen originals are unchanged. No further extraction rewrites of132/133/224/226/227/228 will be attempted. Prior blockers remain as in RESUME-HANDOFF.md.

Required gate order: three ELF pins, optimized native gate (split bench), fixture comparison against37e5e133f8, cumulative cost projection. If cost exceeds2%, restore crates/ fromc97270adc2 and continue with that source. Prior valid projection worst+1.906124819%. Expected heavy time: SBF/native compilation, then native microbenchmarks and fixture proof generation; no elimination gate is added.

## Result: rejected repair, mandatory fixture stop

The two-line repair above is rejected: adding append20 was my error. Frozen append has20 steps, not21. With private21 and append21, the candidate produces129 links. All ELF pins pass; native gate exits101 Err(Shape), so no fixture-byte/cost/Lean stage follows. Detailed receipts and unchanged obligations are in RESUME-HANDOFF.md. Source1be0505afc must not be adopted.85 Lean attempts remain;0 Kani used.
