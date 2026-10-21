# Transparent PairCut field-reader extraction candidate

This focused Aeneas run keeps the normalized v23 PairCut harness but makes
`weights.field` transparent with the body copied byte-for-byte from the pinned
`weights.rs:10` snapshot. It also makes only `WideExact::from_le_bytes` an
opaque unreachable type stub so Charon can check and lower the helper shape.

The extracted LLBC has `has_errors = false`, and the generated Lean includes a
transparent `weights.field` definition with the checked offset arithmetic,
slice indexing, `from_le_bytes`, and `Option.unwrap` sequence. The generated
`push_byte_products` loop retains the read, scratch index, push, error mapping,
`Try` branch, and Continue/Break ordering.

This is a **candidate harness**, not an extraction of the unchanged complete
current `Weights::pair` method. The caller is normalized v23, and the harness
still has explicit opaque or stubbed arithmetic, EbyK `new/push/finish`, and
other helper operations. In particular, the decoder itself is an unreachable
opaque stub. The result does not establish a theorem equating generated code
with the external `weights.field` axiom in the earlier PairCut artifact, nor
does it establish full current-source/Std refinement. No production source was
changed.

`manifest.json` records the source/tool/admission/output pins. The original
LLBC JSON is intentionally not copied into this source-only packet; its hash,
size, error status, and declaration counts are recorded in the manifest.
