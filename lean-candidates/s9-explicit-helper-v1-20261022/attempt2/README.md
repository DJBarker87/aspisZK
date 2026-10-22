# S9 explicit helper candidate, attempt 2 (source-only)

This is a reviewed revision of the isolated candidate. It changes only `factored_s2_libra_weights` in the current admitted `weights.rs` blob. The public generic `kpowers` helper and all other functions remain byte-identical. The production/research worktree was not changed; no compile, extraction, benchmark, or deployment was run.

The frozen base SHA-256 is `28b558ffa9f5b004188c7f50b1597fe681186f54fb4d52a3bd125df4f2481137`; candidate SHA-256 is `9338607afd636f43b3b830bbf9cf3cc0ced1fa7cc78b266282969e519577bccf`. `tools/check_candidate.py` verifies those exact base bytes, constructs the one permitted helper replacement, and requires the candidate file to equal that expected source byte-for-byte. It also confirms that the helper call inventory is unchanged and that its body no longer calls `kpowers::<4>` or `core::array::from_fn`. Run from this folder with `python3 tools/check_candidate.py`; it passes. `helper.patch` contains the only source delta.

For each side, the new scalar-power locals retain the old `kpowers::<4>` multiplication schedule: `ONE * seed`, `q1 * seed`, `q2 * seed`, and `q3 * seed`; the resulting array is `[q0,q1,q2,q3]`. `_q4` intentionally retains the fourth product operation even though its value is unused, so the selected P6 trace can match all four multiplication calls without a new skipped-call argument. The terms are still exactly `ap1[PERM[r]].mul_qm31(high_powers[r]).mul_m31(QUARTER)` for each `r` from 0 through 3, written as explicit locals and an array literal. The high-power calculations, scalar factor, additions, side branches, updates, and loop remain unchanged.

## Proof and gate obligations

1. Extract this exact candidate source and confirm the generated helper body has the same ordered four low-power `qmMul` calls and four term expressions. The old LLBC body cannot be claimed to represent this source without a candidate-specific source/body pin.
2. Prove the direct low-power array agrees with the selected `kpowers` P6 trace's output on the same seed, retaining all four operation outcomes and the same final array.
3. Prove the explicit term array agrees with the four callback results from the retained concrete term semantics, preserving indices, operation order, and output array.
4. Use the two array equalities to transport the existing active-body and whole S9 proof. This rewrite does not establish generic `core::array::from_fn` semantics and does not change the source-library obligations outside this helper.
5. Only after those steps are checked, run optimized native equivalence and the current SBF artifact plus six-fixture/stack gates on an isolated overlay. Reuse the approved current-overlay build cache and source inputs; collect fresh admission and exact scope receipts first. The user's CU allowance is a review ceiling, not a result. No CU claim is made for this candidate.
