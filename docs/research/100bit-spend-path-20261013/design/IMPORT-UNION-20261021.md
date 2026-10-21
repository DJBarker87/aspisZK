# Combined cone imports — 21 October 2026

Branch `codex/cx-import-coll-20261021`, base `f01405274`. Existing modules,
Session A candidate directories, other workers' files and shipped sources are
read-only. All experimental sources and receipts are under
`evidence/import-coll-20261021/`. This is an import integration experiment;
no soundness premise is removed.

## Inventory

The inventory enumerates kernel environment constants in each of the three
retained R22 audit groups, including implicit declarations, readers,
constructor/projection/recursor declarations and wrappers. It compares names
and defining module, excluding shared Lean/mathlib/Aeneas library owners.
`duplicate-declarations.json` contains every differing-owner overlap in this
union. Common imports with the same owner are intentionally not collisions.
This scope is the reported three-group obstruction, not every archived
extraction elsewhere in the repository.

| Name | Defining modules / extraction |
|---|---|
| `instDiscriminantErrorIsize` | `AspisR1PublicPreparation.Types` (public preparation); `AspisR1S3InactiveSource.Types` (`s3_inactive_source_cut`); `Stage2ContinuationTypes` (`aspis_r1_cost_probe` stage2 continuation) |
| `instDiscriminantVariantIsize` | public preparation Types and stage2 continuation Types |
| `instDiscriminantPhaseIsize` | public preparation Types and stage2 continuation Types |
| `Aeneas.Std.Array.make.eq_1` | `AspisV8R19.SqueezeSourceExecution` and `S3VariantRowBodyProbe` (lazily materialised equation theorem) |

The first three names denote definitions (typeclass instances), not identical
shared types. Their enum types and `read_discriminant` functions already have
different fully qualified names. The common `M31`, `CM31`, `QM31` and layout
spellings are beneath distinct extraction namespaces; there is no additional
shared Types definition name in the enumerated union.

The fourth overlap is allowed: Lean 4.32's `Lean/Environment.lean` explicitly
permits different modules to prove the same theorem with the same type, to
support on-demand equation lemmas. Proof bodies may differ by proof
irrelevance. It must be distinguished from duplicate instance definitions.
The prototype below will check this distinction in the actual union.

The untouched baseline fails with:

```
import AspisR1S3InactiveSource.Types failed, environment already contains 'instDiscriminantErrorIsize' from AspisR1PublicPreparation.Types
```

## Proposed fix and prototype

In progress: qualify discriminant instance names on evidence copies, retaining
the original generated reader and all enum/type/function names. Rebuild the
small dependent wrapper closure into a private object directory, then import
all three audit groups in one uniquely named root module.
