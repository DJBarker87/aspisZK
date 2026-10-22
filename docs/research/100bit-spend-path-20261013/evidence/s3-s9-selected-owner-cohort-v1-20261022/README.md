# S3–S9 selected-owner cohort replay

This packet records the bounded NUC owner-cohort recompilation for the selected S3 field-operation sources against the selected S9 imports. Stage01 (`AspisV8R17.QM31WordTower`) was reused from accepted attempt10; stages02–20 were recompiled in order in attempt23. Before stage02, the complete 5,119-module import union and selected owner hashes were preflighted. Each stage passed a fresh global-admission check. Lean used `-j1 -M4400`; the scope was High=3 GiB, Max=4 GiB, Swap=0. All stages exited zero, with no swap or OOM events.

The `.ir` sidecars are sibling module files (`Module.ir`) and are hash-pinned in the selected owner manifest. The packet intentionally contains no compiled objects.

This result establishes that the selected Lean source-owner cohort compiles in one coherent S9/S3 import profile. It does not establish frozen production caller identity for `weights.field`. The stage20 parser readback theorem is an adapted parser bridge; the source-call/body identity join remains open.

The run used 19 rebuilt targets plus one reused stage01 owner; it was not a whole-package replay. Previous setup attempts and their diagnostics are retained under `remote/failed-attempts/`.
