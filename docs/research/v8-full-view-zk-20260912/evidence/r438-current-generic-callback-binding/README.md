# R438 generic callback binding evidence

This bundle preserves the R438 no-monomorphization LLBC capture, launch and custody receipts, independent capture audit, the completed R437 metadata and borrow inventories, the completed R438 generic binding and source-origin/writeback inventories, and the independent metadata audit. Nested inventory checksum files are byte-preserved. `copy-manifest.json` distinguishes verbatim source copies from authored or generated artifacts, records exact source paths and hashes, and lists the complete package file set.

The R437 inventories remain labeled with their original capture and source functions. R438 generic binding and origin/writeback facts are separately preserved under `generic-inventory/` and `generic-source/`. The origin/writeback inventory records AST places and statements; it does not establish aliasing or source/interpreter equivalence.

Two portable checker replays are kept under `root-launch-a/portable-replay/`. The capture-audit script is derived from the preserved original by exactly three path/output substitutions recorded in `copy-manifest.json`; its separate report passes 13 checks. The metadata checker is a verbatim duplicate of the archived checker and writes its report to a separate replay directory. Original audit reports and nested indexes remain unchanged.

The capture and metadata findings are described in `R438_CURRENT_GENERIC_CALLBACK_BINDING.md`. They establish custody and literal metadata facts only; they do not establish Rust runtime dispatch, Aeneas execution correspondence, or a formal security result. No Lean compilation was performed for this package.
