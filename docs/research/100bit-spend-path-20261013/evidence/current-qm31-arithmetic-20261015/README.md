# Current QM31 arithmetic extraction bundle (interim)

This is a working, unsealed bundle. It includes nine green focused Lean targets and two failed proof attempts. Root may add further checks in a later explicitly recorded bundle revision.

## Extraction stage

The standalone Charon/Aeneas extraction ran against proof revision `ccb6f8463f9411f6fc3ed7e6c5cd53f32c5a42b3`. The staged `field.rs` and `wide_exact.rs` are byte-identical to the proof-worktree sources (SHA-256 `28df5a1a…f5f1baea` and `6260fa9d…c6411d10b`); the only new Rust source is a probe wrapper calling production `QM31::add` and `QM31::mul`. Lock, Charon and Aeneas stages exited 0 without dependency builds. Charon 0.1.223 emitted LLBC; Aeneas `b59d518` emitted 13 nonopaque functions, 3 types, and 1 global. Lean 4.31.0 compiled generated `Types.lean` and `Funs.lean` against cached imports. The original extraction `artifact-pins.json` is retained unchanged; its `not_run` field reflects preparation before the extraction attempt, while the later receipts record successful runs.

## Green Lean targets

Generated Types, generated Funs, M31 add/sub, reused `RawReducerNat`, reducer operations, current reducer, tower add, CM31 multiplication, and QM31 multiplication all exited 0. The M31 add/sub log retains two harmless unused-simp warnings, so that proof is not warning-free. CM31's repaired proof explicitly gives the intermediate `(2^32)*(2^32)` overflow bound; no premise changed. The successful QM31 proof has one standard-only axiom report. The two failed first attempts `cm31-mul-a` and `qm31-mul-a` remain with their snapshots, logs, receipts and preflights; their `sorryAx` reports are diagnostics only and are not counted as theorem results.

Every green proof source is retained under `proof-sources/`; per-attempt snapshots remain under `lean-attempts/`. The unchanged `RawReducerNat` source is identified separately. `objects.tar` contains only the nine green objects. `TARGET-RESOURCE-AXIOMS.md` reports wall time, sampled aggregate RSS, process swaps and axiom-output counts for all attempts.

The nine requested current-vs-historical generated blocks match textually after only field-namespace and whitespace normalization; binder names were not rewritten. This does not prove arithmetic equivalence or current Rust/compiler refinement. Historical V8 R17 source pins and normalized block hashes are in `textual-nine-block-comparison.json`. The two copied inventory notes in `reuse-inventories/` are read-only reuse context, not proof closure or an authority for unstated assumptions.

Focused Lean checks used `-M3000`, cached imports, and no dependency replay. Extraction feature flags disabled defaults, R0 op count, R0 R91 audit, and R0 E4 reference. This bundle is evidence for the listed translation and Lean targets only; it does not claim protocol-level source acceptance or cryptographic closure.
