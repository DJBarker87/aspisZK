# R573: Current masked-claim prefix execution

R573 proves the actual generated `begin_state_only_masked_sumcheck` prefix for every native transcript, native QM31 claim, and input slice whose bytes are the exact 18-byte claim record. The record is `[27, 10] ++ qm31Bytes (R196.toBefore (toCurrent q))`.

The theorem preserves all three result paths. An `absorb` failure remains its failure. A generated `challenge_nonzero_qm31` success retains its returned challenge and advanced transcript. Its error is mapped exactly to `ChallengeSampleExhausted`. It does not assume that sampling succeeds, that a claim is canonical, or that any address is fresh.

The proof reuses R196’s exact current writer result after a four-coordinate representation rename. It proves that the generated fixed 18-byte record builder is the same slice and then unfolds only that builder and the error conversion. It also proves injectivity of the current-to-R196 conversion, `claimBytes`, and the defined fixed-state address `t.state.val ++ [0, 31] ++ claimBytes q`.

## Verification

- Canonical source: `lean/AspisV8R19/R573ClaimPrefixExecution.lean`
- Canonical and original draft SHA256: `3c0b57b167b8e7808818bb876e4a6dc4d604f1691f7048aef4f6b16262f24d98` (byte-identical)
- Source revision: `a972625eb882ed910cb00800df166a2a62c6ad8d`
- Original focused target: `R573ClaimPrefixExecution.lean`, receipt `aspis-focus-1791082615886238000.receipt.json`
- Original result: exit 0; wall 2.21 s; Lean-child RSS 3,770,988 KiB; swap 0
- Canonical import-path target: `AspisV8R19/R573ClaimPrefixExecution.lean`, receipt `aspis-focus-1791082751445913000.receipt.json`
- Canonical result: exit 0; wall 2.26 s; Lean-child RSS 3,770,600 KiB; swap 0
- Both runs: `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`; Lean `-j1 -M4500`.
- All 23 focused attempts, including setup and proof failures, their exact source snapshots, logs, and receipts are preserved in `evidence/r573-current-masked-claim-prefix/attempts/`. The final source had no warnings, `sorry`, `admit`, or declared axiom.

The complete final `#print axioms` output is retained in both successful logs. The representation and injection theorems use only `[propext, Classical.choice, Quot.sound]`; `begin_exact` additionally depends on `core.fmt.Formatter`. This is the opaque generated standard-library type inherited through R569, not a new admitted theorem. Its pinned definition is copied from R569 evidence at `evidence/r573-current-masked-claim-prefix/dependency-r569/Aeneas/Std/Core/Fmt.lean` (SHA256 `26ac770dbf97ae2947a968818c307044262756bd67275101ac0c34fb817a81ce`): line 13 declares `axiom core.fmt.Formatter : Type`.

The direct generated dependency is `AspisR569MaskedClaimCompleteConsts.Funs`, SHA256 `23f95e37f92a525c6d24392048d77953cc7dd47cf455ad48dcb5124a55fb13a6`; the exact Funs and Types source copies, all direct import pins, runner, source snapshots, logs, receipts, and recursive SHA manifest are in the evidence directory.

## Boundary

This is an exact record-construction, native absorb/nonzero/error/state equality. `nativeAddress` is injective only as the defined byte expression. R573 does not connect that expression to a flattened actual hash-call address, establish an old-to-native sampler bridge, prove oracle chronology or adaptive freshness, or make a privacy or security claim. The first remaining proposition is the actual flattened hash-call/address connection and then the shared-oracle adaptive trace law.
