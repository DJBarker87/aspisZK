# Focused mask bridges and terminal row components

These four targets passed on the pinned Lean 4.32 NUC workspace, serially in
4 GiB high / 6 GiB max / zero-swap scopes. This archive is separate from the
144-target dependency reconciliation. It contains exact source snapshots,
receipts, import pins, logs and compiled outputs. The lead independently
checked all four source/output/receipt pairs and parsed the raw axiom reports.

| Target | Controller seconds | Peak process RSS KiB | Axiom reports |
|---|---:|---:|---:|
| `ExtractedMaskSemanticBridge` | 3.321 | 4,061,732 | 1 |
| `ExtractedMaskSemanticBridgeConcrete` | 2.880 | 4,045,296 | 2 |
| `RawPoseidonExternalRows` | 1.775 | 3,331,732 | 3 |
| `RowCallbackSlice` | 1.365 | 2,601,652 | 0 |

All six emitted reports contain only standard Lean axioms. The generated
callback slice emits no reports; it is counted as a successful compilation,
not an audited behavioral theorem. All targets exited zero with zero process
swaps. Exact source hashes, wall-time strings and direct imports are in
`root-review.json` and the archived receipts.

The two mask rechecks use the newly reconciled dependency outputs. Their
compiled bytes happen to match the previous provisional objects; the new
receipts record the current imported objects. The source contracts still
assume canonical source inputs and do not establish accepted-verifier
composition. Historical source-admission evidence is the union of the new
queue records and the earlier retained successful receipts, not this four-file
batch alone.

`RawPoseidonExternalRows` proves the four raw matrix formulas equal the
existing `R0P.poseidonMat4` model. With arbitrary stored U32 inputs, each raw
limb is below `2^35`, hence below `2^62`. These are symbolic model lemmas;
they do not themselves prove the generated callback implements those formulas.

`RowCallbackSlice` includes the exact generated closure type, callback bodies
and trait instances from candidate G. The lead independently checked both
selected spans against the pinned complete generated files. Only the module
prelude is supplied separately. The initial `import Aeneas` preflight failed
because the cached umbrella module was absent; the preserved replacement uses
`import Aeneas.Std`. No generated declaration body changed. The slice omits
the full terminal function, `from_fn`, parent array-map and matrix loops; it
is an explicitly named component, not an alternative complete verifier.

The complete terminal semantic proof, external-library model correspondence,
candidate production-source adoption and fresh CU measurements remain open.
