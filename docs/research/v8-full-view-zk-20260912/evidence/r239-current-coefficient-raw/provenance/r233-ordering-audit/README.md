# R233 ordering-root context (read-only)

Pinned Charon checkout: `cb50ff16b9f1066b8a97dc06da704de2da2fa41c`.
This is a source inspection only; no extraction, translation, build, or source edit was performed.

## Finding

The four exact plain `--start-from` paths successfully resolve and enqueue translation roots, but the resulting root `ItemId`s are discarded before the rustc-independent transform context is built. `TranslateCtx` has `id_map` and `reverse_id_map`, and `register_and_enqueue` returns the typed ID; however, `enqueue_module_item` binds it to `_` at `translate_items.rs:301`. `translate_crate.rs:965–974` calls that method for each resolved `DefId`. At `translate_crate.rs:1038–1043`, the handoff to `TransformCtx` retains only options, translated declarations, and errors. `TransformCtx` (`transform/ctx.rs:14–20`) has no root-ID field.

Ordering then independently seeds its graph in `reorder_decls.rs:303–317` by scanning `translated.all_items()` and matching each item name against `ctx.options.start_from`. This is the source of R231's empty `ordered_decls`: the plain method paths resolve for translation but do not match the emitted inherent-impl item names in this matcher. The visitor traverses declaration dependencies from those seeded IDs (`reorder_decls.rs:319 onward`); only after graph construction does the reorder pass install `ordered_decls`.

If repairing Charon itself, the narrow plumbing point is to retain IDs returned by `register_and_enqueue` for resolved roots, carry that set through `translate_crate.rs` into `TransformCtx`, then seed `compute_declarations_graph` from those IDs rather than re-matching textual names. This is an architectural alternative only; no patch was made. Lead selected a separate metadata-only ordering generator rooted at exact extracted Fun0–3, with explicit failure checks, leaving all LLBC bodies/types/options unchanged.

## Evidence and limits

Raw source excerpts and full source-file SHA-256 values are in `root-id-context-excerpts.txt` and `pinned-charon-excerpts.txt`. Excerpt hashes: root-ID context `dcebb862c7b96862099601ecb289032757659cbae7363aef7cf6d73a4988328b`; pinned reorder/matcher/resolver `9d8a38f59dc75acbcdbcdd707172619c1c1fc8703ed8238010d3d105cf791563`.

The R231 LLBC artifact SHA-256 is `ab72ee9cb72ec543bc8a86f5fc2a627cd3c5847eeed46c049d78ab25182294f8`; the corresponding R232 translation JSON SHA-256 is `2fa4f084f8e9d5d1df7c521253e686ceb5c4ec70f770b04bf1709b001f190274` and had empty Types/Funs arrays. Ordering metadata alone cannot establish source semantic correspondence, theorem premises, or proof closure; those require review of actual emitted declarations and a focused Lean axioms audit.
