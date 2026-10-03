# Pinned Aeneas pointer-model and function-selection inventory

Read-only source inventory for the pinned Aeneas translator and Lean library used by this campaign. No build, translation, Lean job, or source modification was performed. The source copies, hashes, line excerpts, commands, and statuses are retained here.

The configured Lean library's `Aeneas.Std.RawPtr` source says raw pointers are not materially modeled: `RawPtr T M` is a wrapper with one value field, and `RawPtr.cast_scalar` returns `Result.fail .undef`. The exact source is preserved at `source/Aeneas/Std/RawPtr.lean` (SHA-256 `752bb5df…f82f47`). `Aeneas.Std.Core.Ptr` contains the alignment enum, `Layout { size, align }`, and `GlobalAlloc.alloc/dealloc` signatures, but no pointer arithmetic. The pinned Slice model imports RawPtr; its unchecked pointer indexing operations return `.fail .undef`, while the generic `Slice.get_unchecked` body is `sorry`. These are literal library-source observations, not a semantic adequacy judgment.

The pinned Aeneas OCaml source search for `NonNull`, `RawPtr`, `size_of`, `offset_from`, and pointer-offset names produced no matching lines (the saved `rg` command exits 1 for no matches). Its `Main.ml` option table has output/backend, diagnostics, sequencing and related settings but no per-function translation selector. `Translate.ml` obtains all functions from `trans_ctx.fun_ctx.to_extract` and processes that list in its opaque/transparent translation passes. `extract_fun_decls` controls a declaration category in output configuration; the inspected lines do not show a per-function selection mechanism.

The saved R429 Charon extraction command demonstrates the separate extraction-stage selectors `--start-from crate::freeze` and repeated `--include` paths, including iterator and slice-fold declarations. This records Charon's input-graph selection in that command; it does not establish an Aeneas per-function translator flag or determine whether a narrower LLBC input avoids any particular translation failure.

For comparison, the already saved pinned Rust std inventory in `.r21-scratch/r429-actual-freeze-fold/std-fold-inventory/` identifies the selected `core::slice::iter::fold` source's pointer-related dependencies and hashes: `NonNull::add/as_ptr`, raw-pointer dereference/shared borrow, `offset_from_unsigned`, `SizedTypeProperties::IS_ZST`/`size_of`, and `usize::unchecked_add`. Its scope notes explicitly avoid Rust execution, pointer-safety, selected-type layout, or Rust-to-Lean correspondence conclusions. This report does not make those conclusions either.

## Pins and files

- Aeneas candidate source root: `/home/dombarker/project-offloads/aspis-r425-unit-constant-candidate-20261002-a/src`; launch revision recorded in the R425 main-build receipt is `ee7ba72da456d5f353bca9f6739b23750a5dfffa`; binary SHA-256 `eadb205f…ca9b01`.
- Configured Aeneas Lean source root: `/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/aeneas-full/backends/lean`; the RawPtr module SHA-256 is in `source-hashes.json`.
- Source excerpts are in `aeneas-selector-source-excerpts.txt` and `slice-pointer-model-excerpts.txt`. Complete RawPtr, Core.Ptr, and Slice source files are copied under `source/`.
- `r429-charon-selection-command.json` is copied from the saved R429 command receipt. `aeneas-pointer-api-search.txt` and `.status` preserve the source-search result and exit status.
