# TTraitType loop-join guard review

This is an independent predicate-level review of the scoped candidate branch
in the NUC tool copy
`/home/dombarker/project-offloads/d18-aeneas-reborrow-v1-20261022/aeneas-trait-guard-v2/interp/InterpMatchCtxs.ml`
(SHA-256 `7a23c3abc469212b14c2ec1ada3997c89fc65b418535ba8be01682cb4b5d4cd3`).
It does not rebuild or execute Aeneas. The same candidate source is already
exercised by FS's bounded v2 run.

The added `TTraitType` case must only match a structurally identical
projection, and only when the type walker reports no regions in either input.
That guard is conservative relative to `TAdt` and `TRef`: those branches
recursively reconcile corresponding region lists with `match_regions`, while
`TVar` requires equal variable IDs. The projection branch does not call
`match_regions`; returning `ty0` is appropriate only when it cannot omit a
region reconciliation. `Utils.phys_eq` is a pointer-equality fast path with a
structural-equality fallback, so separately allocated but structurally equal
region-free projections are accepted. Different clause references, trait or
associated-item IDs, trait-reference generic arguments, or associated-type
(including GAT) arguments fail the complete structural comparison.

Adversarial contract tests are in `test_trait_type_guard.py` and can be run
with `python3 test_trait_type_guard.py`. They model `phys_eq` as structural
equality, and exercise clause, item, generic-argument, GAT-argument, nested
region, and non-`TTraitType` rejection. These tests are not a substitute for
the compiled matcher run.

One exact limitation: `TypesUtils.ty_has_regions_in_pred` intentionally skips
`TDynTrait` when `Config.type_analysis_ignore_dyn = true` (currently true in
the inspected tool source). Thus the guard's “no regions” premise is relative
to that existing type-analysis traversal, not a universal walk into dyn-trait
internals. The target `Try::from_output` projection contains no dyn trait, but
this candidate should not be generalized to projections whose nested dyn
trait regions need reconciliation. If the branch is later widened, this
limitation needs a separate region-complete predicate or a stronger shape
restriction.
