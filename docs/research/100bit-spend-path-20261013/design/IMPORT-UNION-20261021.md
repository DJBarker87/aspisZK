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

The evidence-only `ImportUnionNamedDiscriminant` adapter calls the pinned
`Aeneas.Discriminant.generateReadDiscriminantCmds` and elaborates its reader
command unchanged. It replaces the anonymous instance command with
`<fully-qualified-enum-name>.instDiscriminant`. On copies only, the S3 and
stage2 Types modules import the adapter and replace `@[discriminant isize]`
with `@[import_union_discriminant]`. All five affected enum readers retain
the original generator logic (S3 Error; stage2 Error, Variant, Arity, Phase).
Public-preparation Types/Funs and the entire main group are reused unchanged.

Thirteen copied modules are rebuilt, bottom-up, into
`/tmp/codex-cx-import-coll-20261021-objects`; this directory alone overrides
the old S3/stage2 objects. No shared cache is written. Wrapper changes are
only additional axiom-print commands; statements and proofs are unchanged.
`copy-provenance.json` pins every original and copied source.

| Focused check | Exit | Wall (s) | Peak RSS (bytes) | Swaps |
|---|---:|---:|---:|---:|
| Untouched union baseline | 1 | 5.567 | 2,317,189,120 | 0 |
| `ImportUnionAllConesCx20261021` | 0 | 6.606 | 3,234,267,136 | 0 |
| `ImportUnionHeadlineCx20261021` (R19 + all cones) | 0 | 7.200 | 3,558,064,128 | 0 |

The all-cone module imports **all three** retained R22 audit groups in one
Lean environment and prints 60 standard-axiom audits. The headline aggregator
additionally imports the unchanged `R1FinalSoundnessBinPerQueryR19` and audits
its `final_soundness` theorem to `[propext, Classical.choice, Quot.sound]`.
The equation theorem overlap coexists, as Lean's import implementation allows.
These are focused integration checks, not a replay of the full frozen manifest.

Every attempt uses the requested local toolchain, `-j1 -M4400
-DElab.async=false`, the global mkdir lock, and `/usr/bin/time -l`.
Receipts include source revision/hash, immediate-object dependency
fingerprint, exact command/path, exit, wall, peak RSS, swaps, complete axiom
output and errors. Three initial adapter elaboration errors are retained;
the fourth adapter version passes. There was no memory failure or cap raise.
