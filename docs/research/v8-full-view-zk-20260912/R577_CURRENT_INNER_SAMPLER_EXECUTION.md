# R577 current inner sampler execution

The actual selected ordinary QM31 inner sampler now has a compiled, error-preserving correspondence for its body, fuel-bounded retry loop, and exact eight-attempt range. The proof carries only the justified incoming cursor bound `j.val ≤ 8`; each continuing step derives the next cursor and range from the R137 source read and rollover lemmas.

The proof covers the generated source body’s checked index arithmetic, block squeeze, four-byte read, acceptance/retry branch, transcript and block state, exhaustion, and every `fail`/`div` result. The range theorem preserves the actual stopping behavior. It composes the R569 captured actual-source sampler with the existing R169/R137 sampler bridges.

## Verification

- Exact target: `AspisV8R19/R577NativeInnerSamplerExecution.lean` (the NUC compile output is `lib/AspisV8R19/R577NativeInnerSamplerExecution.olean`).
- Target source SHA-256: `28642fca8289dbc82eb2f4ff30142f201bdd711154d63114f7933ed13ff56efb`.
- Source revision recorded by the focused runner: `35c57c8989c08664ebc43919409556a4686c530a`.
- Pinned Lean: 4.32.0 cached workspace, `-j1 -M4500`.
- Run: `1791090066479470000`; exit 0; wall time 2.85 s; GNU-time Lean-child peak RSS 3,776,780 KiB; swap 0. Compiled cache artifact SHA-256: `f92f46b65b78327df20083a4238a145ee44eb324e8f6a02aa8935122347f99e6`. A prior success under `lib/docs/research/...` was a wrong output path and is retained as an invalid target attempt; it is not the release check.
- Limits: `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`.
- The complete compile log, source snapshot, runner receipt, direct imported-source hashes, runner, and all prior R577 attempts are retained in `evidence/r577-current-inner-sampler-execution/` and listed in its SHA-256 manifest.

## Axiom audit

The successful canonical-target compile directly printed these complete axiom results:

```text
nativeSqueeze_execution: [propext, Classical.choice, Quot.sound]
nativeSqueeze_map: [propext, Classical.choice, Quot.sound]
sourceBody_cont_index_bound: [propext, Classical.choice, Quot.sound, core.fmt.Formatter]
currentBody_cont_index_bound: [propext, Classical.choice, Quot.sound, core.fmt.Formatter]
sourceBody_cont_range: [propext, Classical.choice, Quot.sound, core.fmt.Formatter]
currentBody_cont_range: [propext, Classical.choice, Quot.sound, core.fmt.Formatter]
currentBody_exhausted: [propext, Classical.choice, Quot.sound, core.fmt.Formatter]
body_map: [propext, Classical.choice, Quot.sound, core.fmt.Formatter]
loop_map: [propext, Classical.choice, Quot.sound, core.fmt.Formatter]
eight_attempts_map: [propext, Classical.choice, Quot.sound, core.fmt.Formatter]
```

`core.fmt.Formatter` is the pinned Aeneas standard-library opaque **type** axiom, not a proposition or proof premise: `evidence/r569-masked-claim-execution/aeneas-source/Aeneas/Std/Core/Fmt.lean`, SHA-256 `26ac770dbf97ae2947a968818c307044262756bd67275101ac0c34fb817a81ce`, lines 11–13 declare the Rust type mapping and `axiom core.fmt.Formatter : Type`. The R569 generated inner body (SHA-256 `23f95e37f92a525c6d24392048d77953cc7dd47cf455ad48dcb5124a55fb13a6`, lines 291–292) passes `core.fmt.DebugTryFromSliceError` to `Result.unwrap` after the checked 4-byte conversion. The formatter type enters through that existing error/debug witness dependency; the R577 proofs do not invoke formatting behavior or assume a formatting proposition. There is no `sorryAx` in the successful source snapshot. Earlier diagnostic and failed attempts are retained separately and are not part of the proof result.

## Proven boundary and next obligation

This proves execution correspondence for the selected inner ordinary QM31 loop. It does not yet prove the outer nonzero-QM31 wrapper, the full selected sampler and callback chronology, shared-oracle behavior, or privacy/security. The next source proof is the outer ordinary/nonzero sampler composition and its actual transcript/error-state correspondence.
