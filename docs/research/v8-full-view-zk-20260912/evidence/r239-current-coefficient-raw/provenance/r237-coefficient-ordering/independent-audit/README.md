# Independent R237 declaration-order audit

This is a structural audit of the R237 LLBC metadata rewrite only. It does not run Aeneas/Lean and establishes no source-semantics correspondence.

`audit_independently.py` verifies the exact R231 input and R237 output SHA-256 values; decodes hash-cons references; compares the complete JSON after removing only `translated.ordered_decls`; follows typed ADT, regular function, and global references from Fun IDs 0–3; separately checks the explicit Fun `ItemSource::TraitDecl` dependency rule; verifies all reachable declarations appear once, dependency-before-user order, no cycles/missing refs/trait refs; and compares its edge and integer-id inventories against the existing generator audit. It also checks the complete Type/Fun/Global declaration rows are unchanged.

The pinned source excerpts are from Charon revision `cb50ff16b9f1066b8a97dc06da704de2da2fa41c`, file `charon/src/transform/add_missing_info/reorder_decls.rs`, SHA-256 `8a1176e29a51a83c82ff5a7df2aa11021e3e0c254e9fd6c656c0a92314ba2632`. The excerpt covers typed visitor edges, skipped `ItemMeta`/`ItemSource`, Fun-specific traversal (including the TraitDecl source edge), Type/Fun/Global traversal, and ordering behavior.
