# R430 R429 C fold operation inventory

Read-only AST inventory from `.r21-scratch/r429-actual-freeze-fold/root-launch-c/saved-output/R429ActualFreezeFold.llbc` (SHA `c7c658bff6e44b6bf8397ea1bc7d37f05f3d33810cffc72ae5eaa0bff06d7465`, `has_errors=false`), R429 C root `crate::freeze`, selected Fun70 `core::slice::iter` fold. This does not assign semantics to operations or choose a normalizer.

Fun70 source span is `core/src/slice/iter/macros.rs:259:12–289:13`. The inventory includes every recursive occurrence of `UnaryOp`, `BinaryOp`, `Assert`, and `Abort` in Fun70’s body, with full JSON path, containing statement ID/span and raw payload. Counts: {"Abort": 8, "Assert": 2, "BinaryOp": 7, "UnaryOp": 14}. Each call row retains callee reference, arguments, destination, and complete `on_unwind` tree; the other pointer/word-related tags (`Ref`, `RawPtr`, `NonNull`, pointer metadata, deref/projection/index) are listed separately.

Related exact function rows include IDs 113, 114, 115. Types include QM31 Type2, Iter Type42, NonNull Type58, and PhantomData Type59 with their raw layouts/definitions. Source-file IDs map to rustc source paths in the JSON.

See `inventory.json` for raw paths and rows. It is an extraction-custody inventory only: it makes no assertion about pointer provenance, bounds, checked arithmetic, panic equivalence, or error behavior.
