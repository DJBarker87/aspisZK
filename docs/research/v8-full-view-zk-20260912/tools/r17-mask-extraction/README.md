# Focused actual-source mask extraction

This dependency-free crate wires unchanged `field.rs` and
`r17_structured_g.rs` files into an extraction-only library. It does not alter
production code or replace loops with a synthetic trace. `corelib` is only a
module alias needed by the research source. Source pins are enforced by run.sh.
Extraction excludes `cfg(test)` bodies; no runtime arithmetic test is claimed.

Run run.sh with a directory containing the two pinned files and a fresh output
directory, inside a Linux scope with MemoryHigh=4G, MemoryMax=6G,
MemorySwapMax=0, TasksMax=128. The script uses the cached pinned Charon tool,
Rust nightly-2026-06-01, one job, offline/locked release compilation.
Record the LLBC hash, then pass it to translate.sh with a fresh output path in
an equivalently bounded scope. Neither script overwrites existing outputs.

The first actual-source translation succeeded but is NOT a compiled theorem.
It emitted external placeholders for Iterator.map.default and Map.next, and
warnings concerning map/zip/collect/rev runtime trait information. Do not copy
FunsExternal_Template.lean into FunsExternal.lean or accept its axioms. Supply
justified runtime models first, then compile the smallest dependency and caller.
The translated field types are in a fresh namespace; their relation to the
previous arithmetic projection must be checked, not inferred from names.

Pinned evidence, command results and the remaining obligations are recorded in
../../R16_SOUNDNESS_OBLIGATIONS.md. Raw extraction artifacts remain in the
task-owned Linux workspace identified there, outside accepted Lean targets.

Follow-up focused checks:

- `check_types.sh RAW_TYPES FRESH_TASK` compiles actual generated declarations
  with the sole import narrowed to cached Scalar.Core. Use the same bounded
  scope; this new runtime-import target has a preselected Lean -M3200 limit.
  `AuditTypes.lean` separately audits the four emitted types in that workspace.
- `check_closure.sh TASK RAW_FUNS` expects check_closure.py and
  AspisV8R17/MaskClosureWriteback.lean in TASK. It checks the whole Funs pin,
  exact schematic closure body and two mutation controls, then compiles at
  -M1800. This proves the specific closure's borrow-closing algebra, NOT the
  full generated closure trait instance or caller.

The generated FnMut/FnOnce and map/collect return shapes differ from cached
runtime interfaces. Applying the actual returned write-back is essential;
do not erase it merely to obtain a type-correct adapter.

`stage_iterator.py RAW_MODULE FRESH_TASK` now supplies an explicit candidate
compatibility stage. It records every count-checked replacement and extra
model hash. Run the same command with `--check` to validate without writing.
`run_iterator.sh TASK CLOSURE_WORKSPACE TARGET` compiles one of Types,
IteratorCompat, IteratorLaws, CollectorLaws, Funs or AuditCaller in a caller-supplied bounded
zero-swap scope; dependencies must already be compiled in that task/cache.
Run the smallest new dependency first, then Funs, then the audit. The full
staged caller compiles without imported template axioms, and the typed
closure/map step and zip forward/write-back lemmas compile.

CollectorLaws proves unconditional observable Result equality with the cached
list/vector collectors (including failure and divergence); AuditCaller now
instantiates that equality in the generated mixing_row. Compile CollectorLaws
before AuditCaller. No successful-termination premise is introduced.

This stage is not a certified compiler pass. Concrete Rust collection and
allocation behavior, field projection correspondence and full loop invariants
remain open. Source inspection distinguishes default zip next from TrustedLen
vector collection; see the ledger. Compilation/axioms audits do not close the
remaining source-to-model or global security gaps.
