# R438 independent metadata audit

`verify_metadata_audit.py` independently decodes the frozen R437 LLBC JSON and verifies the complete function-slot table and descriptors against the raw `translated.fun_decls` array. It confirms all 159 slots: 156 populated (91 `TopLevel`, 60 `TraitImpl`, 5 `TraitDecl`) and absent slots 6, 127, and 131. The unique function matching `TraitImpl 35` / method slot 0 is function 112. Its source entry names `call_mut`, refers to trait 3, and has `reuses_default=false`.

The checker recursively locates exactly one matching call in function 70 at `$.Structured.body.statements[10].kind.Switch.If[2].statements[7].kind.Loop.statements[27]`. Trait declaration 3's method name is `call_mut`, while its serialized `methods` list and trait implementation 35's `methods` list are both empty in this capture. The complete call reference remains in the inventory's `selector-inventory.json`.

The checker verifies all copied full Charon source files against their recorded SHA-256 pins and verifies the inventory's own checksum list. Generated-AST source files are represented by remote source hashes and retained excerpts, not full local copies. The pinned translation source excerpts describe the monomorphization early-return paths and the later `.methods.get(method_id)` lookup; this audit reports those source facts only. It does not establish runtime dispatch, executable closure invocation, or source/model equivalence.

Run from the worktree root:

```sh
python3 .r21-scratch/r438-fnmut-source-selection/metadata-audit/verify_metadata_audit.py
```

The checker writes `audit-report.json` beside itself. It accepts `--inventory` and `--out` for use with an archived copy. No extraction, translation, compilation, or proof was run for this audit.
