# R437 pinned Aeneas pointer-source boundary

Read-only source inventory, reusing saved R430 source copies and inventories. Exact copied file hashes and byte counts are in `inventory.json`; selected numbered code excerpts are in `source-excerpts.txt`. `source/` contains byte-identical copies of the inspected R430 files plus five exact read-only copies fetched for the requested Pattern/NotNull schema check. Their paths and hashes are listed in the inventory.

The pinned Lean library has a list-facing `Slice` model, while its `RawPtr` is a small wrapper whose scalar cast returns `fail .undef`. The interpreter source explicitly rejects raw-pointer dereference, does not dispatch raw pointer rvalues to a supported evaluator, reports aggregate raw pointers unsupported, and rejects `AddChecked` and `Offset` in the symbolic binop path. Its generic concrete scalar branch also has no implementation for these operations and falls through to an unimplemented-operation failure. Unchecked slice-pointer APIs return `fail .undef`; the generic `Slice.get_unchecked` definition and an associated spec contain `sorry`.

Ordinary Rust references, shared/mutable borrow bookkeeping, function-frame handling, and a restricted symbolic shared-global path do exist in these sources. The global path is not a raw-pointer model, and this inventory does not infer a usable pointer, frame, alias, or source-correspondence contract.

No builds, translations, proof checks, or semantic decisions were made.
