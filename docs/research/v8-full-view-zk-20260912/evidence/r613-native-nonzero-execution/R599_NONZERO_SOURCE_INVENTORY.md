# R599 nonzero sampler source inventory (read only)

No extraction, compile, or semantic correspondence claim was made in this inventory.

## Pinned generated inputs and hashes

- R569 generated functions: `docs/research/v8-full-view-zk-20260912/lean/AspisR569MaskedClaimCompleteConsts/Funs.lean`, SHA-256 `23f95e37f92a525c6d24392048d77953cc7dd47cf455ad48dcb5124a55fb13a6`. Generated metadata names the frozen R569 source root `/home/dombarker/project-offloads/aspis-r569-masked-claim-20261004-b`; transcript declarations refer to that crate snapshot.
- Current selected R117 R156 functions: `docs/research/v8-full-view-zk-20260912/lean/AspisR156FullFreeze/FunsCore.lean`, SHA-256 `5ef8405549c6feff405715a6697ffff9a370610d5dc116fc452a1046fae0c1f2`.
- Existing current-model execution proof: `docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/R173NonzeroExecution.lean`, SHA-256 `ac293547a139a0bc4e1faf74461913fda86be31a0895a9fea1cbd13c6e001aba`.

## Native R569 source declarations

In R569 `Funs.lean`:

- `aspis_core.transcript.Transcript.challenge_nonzero_qm31_loop.body` (around lines 426–455), signature `Range U32 → Transcript → Result (ControlFlow ((Range U32) × Transcript) ((core.result.Result QM31 ChallengeSampleExhausted) × Transcript))`.
- It pulls one range item. On exhaustion it returns `done (Err (), self)`; otherwise it invokes `challenge_qm31`. On `Ok val`, it calls `core.cmp.PartialEq.ne.trait_default` with the QM31 equality instance and `QM31.ZERO`; true stops with `Ok val` and the advanced `self1`, false continues with `iter1` and `self1`. On sampler `Err`, `CoreOpsTry.branch` takes the break path and `FromResidual...from_residual` returns the same exhaustion result with advanced `self1`.
- `aspis_core.transcript.Transcript.challenge_nonzero_qm31_loop` (around 463–473) runs the body over the supplied range.
- `aspis_core.transcript.Transcript.challenge_nonzero_qm31` (around 482–489) has signature `Transcript → Result ((core.result.Result QM31 ChallengeSampleExhausted) × Transcript)` and calls the loop over `{ start := 0#u32, end := NONZERO_QM31_RETRY_LIMIT }`.
- The actual captured retry constant is `NONZERO_QM31_RETRY_LIMIT = 3#u32` (line 418).

The zero test is the ordinary `PartialEq::ne` default on the actual generated QM31 `PartialEq` implementation. The generated `QM31.eq` compares `c0`, then `c1` only if `c0` equality succeeds; each `CM31.eq` compares limbs `a`, then `b` only if `a` equality succeeds. The actual `QM31.ZERO` is all four U32 limbs equal to zero. The generated `QM31` trait impl sets `ne` to the shared default `core.cmp.PartialEq.ne.trait_default`.

## Current R156 counterpart

R156 `FunsCore.lean` contains same-named declarations for the nonzero body, loop, and wrapper around lines 1284, 1321, and 1340. Their signatures and branch structure match the R569 declarations: same 3-attempt range constant, ordinary challenge call, nonzero test, stopping/continuing behavior, and propagated exhaustion with the advanced transcript. The R156 bodies call R156 `challenge_qm31`; its selected sampler correspondence is what R598 now binds to the native sampler.

## Existing R173 bridge scope

R173 does not prove a bridge from the new R569 native capture. It provides the current R137-model execution:

- `entry_three`: current transcript wrapper equals three-step bounded loop.
- `ne_map (q : AspisR137Transcript.field.QM31)`: equality-to-zero after the `quartic` conversion equals the R137 QM31 equality-to-zero test. It unfolds `PartialEq.ne`, its default, QM31/CM31/M31 equality implementations and both zero constants.
- `bounded_map`: induction over `n`; handles sampler fail/div, Rust `Err`, and all zero-test fail/div/true/false results, recursing only on false after checking the advanced state.
- `challenge_map`: composes `entry_three`, current R137 bounded loop, and `bounded_map`.

Thus R173 offers a reusable zero-test/three-attempt *current-model* pattern. A native continuation still needs to bind the captured R569 loop/body and native `challenge_qm31` result/state to the R156/current counterpart, preserving all error, divergence, stop, and advanced-state branches. No source-correlation or soundness/privacy conclusion follows from this inventory.
