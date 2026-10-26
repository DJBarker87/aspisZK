# Final allocation report

No requested ledger row was closed. The target is not established.

Branch: `codex/cx-prover-rw-20261023`. Base: `5d97a425c5` (unmerged prover candidate).
Final checked proof-source revision: `8d44f7cf119b1d1b2b841239345072ac91185259`.
No push or merge. No production source or release pin changed.

## Budget and validation

- Lean: **100/100** charged invocations, **73 passes /27 failures**. Input-only refusals are separately recorded and charged zero;23734's missing-file invocation is conservatively charged one.
- Kani: **20/20**, **12 passes /8 timeouts**. No failing comparison was promoted to a certificate, no timeout rerun unchanged, no caps increased. The full table is [KANI-SPLITS.md](KANI-SPLITS.md).
- One final focused cached manifest with complete axioms audit: `R1Z/PV_RW_FrozenManifest`, ID23809, exit0, **24.06s**, **3,185,344,512 RSS bytes**, swap0. All **212 new theorem reports plus the unchanged headline** use standard axioms only. Receipt: [local/23809-receipt.json](local/23809-receipt.json); complete output: [local-23809.log](local-23809.log).
- All69 current PV_RW modules match successful source receipts; all frozen source hashes match v2. Generator `--check`, Python syntax checks, immutable native snapshots, LLBC source-path resolution and strict evidence validation passed.
- This is a focused cached closure check. A coherent source/release dependency replay is not claimed. Native Rust runner's ambient compiler/revision labels are qualified in README; exact input hashes and tool output are retained.

## Proved and measured

The emitted arithmetic step, actual Std initializer/iterator and emitted combined iterator/arithmetic transition feed a genuine Aeneas loop. The composed compression equals the closed owned reference for arbitrary slices and typed arity16, including the complete accumulator/power state, exact Result/failure/divergence, totality, sufficient17 control bound, final-power projection, length independence and symbolic8+8/chunk laws. The equality is consumed by the complete auxiliary caller and `CombinedBodyData.refinement_of_data`.

V163's full data criterion is exactly equivalent to separate proof-byte and audit comparisons once retained state writeback is supplied. Both error layers and divergence remain observable. Neither comparison to a concrete security model is proved.

Sampler receipts supply native limb, array-state iteration, reverse iterator, parser and decoder pieces; emitted step/array-control correspondence, remainder/index invariants, totality and loop bounds are checked. The complete native ordinary sampler/live callback association remains open.

## Before/after and premises

See [BEFORE-AFTER.md](BEFORE-AFTER.md) and [OBLIGATIONS.md](OBLIGATIONS.md).
V164's original whole-helper source association remains open: the full-helper Aeneas probe failed, and native arithmetic state/coordinate gates timed out. V163's concrete whole-model equality remains open. **Ledger rows removed: none (V163, V164, callback rows). Endpoint/deployment premises removed, weakened or renamed: none.** No live callback installation was made; pv-cb assignments/supplied callbacks were skipped.

Two procedural timing deviations are recorded openly in README: the first fission probe overlapped a quiet window before it became known, and retry23753 was approximately10.6seconds short of the required180-second wait. Later deadline checks prevented repetition. Quiet-window refusals and all other input refusals remain in the packet. No marker or shared launcher was edited.

## Stop and next deliverable

Stopped because both budgets are exhausted, rather than on Kani exhaustion or a translator failure alone. Next: obtain a checked association of the original helper's for-loop context to the emitted combined-transition loop, preserving initializer, actual iterator and every final power update; then perform the live op223 join. V163 additionally needs the concrete model term and both exact data comparisons. The pending clarification received no answer; no source-output model was invented.

Source-stage commits through the checked revision:

```
8d44f7cf11 Complete the focused cache prerequisite and combine the final manifest audit
ca2805f032 Prove combined compression control and freeze the focused proof manifest
b75c0ea0a1 Prove actual iterator loop transport and consume compression equality in the body criterion
0c262bacc0 Prove closed compression arithmetic and exact iterator state correspondence
09df2340e2 Prove emitted sampler step invariants and bounded array loop correspondence
bbcc13a0af Prove bounded arity sixteen compression model and retain native split receipts
882c30be11 Isolate compression state step and prove exact fold induction
```
