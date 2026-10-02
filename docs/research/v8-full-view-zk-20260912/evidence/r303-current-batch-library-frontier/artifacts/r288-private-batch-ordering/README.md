# R288 root-Fun0 ordering diagnostic

This is a metadata-only attempt to compute a declaration order for the exact
R283 LLBC, rooted at `Fun 0`. It changes no bodies or type/signature rows and
was never sent to Aeneas. The input has `has_errors=false`; its SHA-256 is
`999fdb4f5a034faf9d4aa11c7a44851b9c79f471d76ae6afb3b92aed0767c8d5`.

The generator mirrors the pinned five-kind declaration visitor in
`pinned-reorder_decls.rs` (SHA-256
`8a1176e29a51a83c82ff5a7df2aa11021e3e0c254e9fd6c656c0a92314ba2632`).
It queues trait default const/method targets for reachability without adding a
dependency edge, as the pinned source does with `insert_node`. It records the
pinned singleton `TraitDecl` self-edge exception and emits no SCC groups. Other
cycles, unknown reference shapes, and missing references fail closed. Missing
vtable metadata is skipped only for absent `Type` declarations referenced from
a `TraitDecl`/`TraitImpl` vtable field whose item label ends in `::{vtable}`;
each such skip is retained in the diagnostic.

The attempted order stops at a self-edge in `TraitImpl 11`, named under `core::iter::range` as an impl item for trait id 11, source file id 28, line 980. Three
serialized method trait-reference paths point back to that impl:
`methods[8].skip_binder.generics.trait_refs[0].kind`,
`methods[42].skip_binder.generics.trait_refs[0].kind`, and
`methods[54].skip_binder.generics.trait_refs[0].kind`. The diagnostic includes
the partial visited set, dependency edges and paths, typed-reference census,
default reachability rows, and vtable skips. No ordered LLBC was written.

The first draft falsely treated a default-reachability traversal as a graph
cycle; it is preserved under `rejected-self-trait-preflight/`. The current
runner queues default targets separately and gets past that false cycle. The
remaining self-edge is outside the expressly permitted singleton TraitDecl
case, so this bundle stops. It does not infer a recursive group or claim
translation, source correspondence, or proof closure.

Follow-up context: the exact original R283 input already carries 109 Charon
`ordered_decls` groups, including the SCC encodings. This failed root-subset
reordering diagnostic is separate and unnecessary for the original ordered
input; its history is preserved.
