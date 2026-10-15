# SemanticHit import join and literal exclusion evidence

This curated bundle preserves the import-owner diagnostic, the SemanticHit import-join compile, the separately checked `LiteralSemanticExcludedLift.excluded_lift`, and all five attempts at the redundant combined `LiteralSemanticLiftNoHit` wrapper.

The `SemanticHit` import join and `LiteralSemanticExcludedLift` are green focused targets. The wrapper attempts a–e are all failures; c/d/e no longer report the generated declaration collision, but fail on an unknown identifier/whnf timeout or whnf timeout. The lead retired the wrapper because the direct `excluded_lift` result supplies the required exclusion. No combined `LiteralSemanticLiftNoHit` compile is green, and this package does not claim one.

Attempt a lacked the cached `MaskSemantics` object. Attempt b then encountered the duplicate generated declaration from `MaskD2Glue`; the diagnostic reports `decisionZ.congr_simp` is owned by `R1SemanticHit`. The import-join target succeeded after the import order change in `SemanticHit.lean`. The provisional `MaskSemantics` import edit was never run and the file remains restored to its pinned source.

The bundle stores receipts, source snapshots, logs, preflights, runner snapshots, explicit direct-import pins, and a deterministic object archive. It makes no probability/security or downstream consumer claim.
