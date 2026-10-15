# Candidate strict parser extension evidence

This extension, sealed after independent root audit, records three final Lean targets: four byte-order lemmas, the strict QM31 decoder refinement, and a combined checkpoint. It preserves six exact attempts (three failed, three successful) and uses source base `6e25cda9d35e52df0980dbcd6744522bd3caaab0`. Attempt sources, receipts, sidecars, logs, and time logs are copied byte-for-byte and hash-matched.

The object archive contains only the three final module objects. Parent candidate-parser objects, direct-import pins, runner files, and environment snapshot are retained under `prior-imports/` and `runner/`; no loose `.olean` files are retained. The extension is separate from the parent bundle and does not alter its seven-target ROOT-VALIDATION scope.

The source patch was isolated when this proof batch was collected. The later v1.52 cost gate passed and the exact rewrite was applied on the research branch; see ../../CANDIDATE-FIELD-PARSER-CHECKPOINT.md for that separate result. Lean checks cover these declarations and their pinned imports; they do not establish Rust compiler correspondence or a full parser/security claim. ROOT-VALIDATION.json records the completed independent audit.
