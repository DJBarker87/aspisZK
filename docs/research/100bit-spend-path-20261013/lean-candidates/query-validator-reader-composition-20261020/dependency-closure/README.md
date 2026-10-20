# Recursive dependency closure (source and evidence only)

This directory adds the native Lean source and attempt evidence needed to review the green query-validator/reader candidate recursively. It contains no `.olean`, `.ilean`, or other compiled object files. Object identities are pinned in `manifest.json` and in the retained per-attempt `preflight.json`/`receipt.json` files.

The collected owners include branch 0/1/2 and boundary soundness, their chunk/no-hit/gate helpers, the generated validator prefix and chunk helper, the reader generated source, and `RawCursorAdvance`. Each native attempt keeps its exact command, preflight, receipt, and `time.log`; source files are SHA-pinned in `manifest.json`.

**Status: dependency conflict remains open.** `AspisR1Stage2AdoptedResume.Types` occurs as two different selected objects in the candidate graph. The reader-compatible source has both `verifier.Error` and `verifier.Reader`; the validator-prefix source has only `verifier.Error`. The sources and object pins are both retained and the hashes are listed under `module_hash_conflicts`. The green composition result must not be treated as a coherent source-owner closure until the selected Type owner is unified and affected dependents are rebuilt or otherwise resolved.

Aeneas/Lean/Mathlib package source trees are not copied here; their exact selected object hashes and paths remain listed in `import-source-map.json` and attempt preflights. Failed diagnostics remain separate from green owners.
