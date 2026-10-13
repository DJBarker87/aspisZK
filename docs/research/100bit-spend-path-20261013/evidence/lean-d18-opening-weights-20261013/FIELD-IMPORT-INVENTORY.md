# Field-tower import cut inventory

Read-only source inspection at worktree HEAD `0dbaf0c8d576a8da71e031b89cef2c9083c67cca`. No Lean compile, cache mutation, or source edit was performed. The source hashes and exact direct imports for the inspected files are in [`FIELD-IMPORT-SOURCES.json`](FIELD-IMPORT-SOURCES.json). This inventory describes import structure and declarations; it does not select a cryptographic premise or establish that a compile will fit the runner's memory limit.

## Narrowest source cut visible

`WideTower.lean:1` has one direct import of `AspisFormal.V5ComponentCQM31TowerExact`; line 11 opens that namespace. That is the single direct edge from `WideTower` into the sampler-bearing exact tower. The existing `AspisV8R15.ExactTowerBase` module is a narrow field-only source counterpart: it directly imports `Mathlib.Algebra.QuadraticAlgebra.Basic`, `Mathlib.NumberTheory.LegendreSymbol.Basic`, and `Mathlib.Tactic.NormNum.Prime`, and declares the same literal `P`, `M31Exact`, `CM31Exact`, `qm31R`, and `QM31Exact` tower plus the M31/CM31/QM31 nonsquare and rootless facts. Its source comment says those base declarations were extracted from the exact tower; the declarations have different fully qualified names.

At the type-expression level, unfolding both sets of abbreviations gives the same `ZMod 2147483647`, quadratic algebra over `-1`, and quadratic algebra over `(2,1)`. The constant `P` is the same literal. The rootless `Fact` declarations and prime `Fact` are separate names/instance declarations in the two namespaces, even though they state the same propositions over definitionally equal types. This is an instance-provenance difference, not a source-level namespace alias.

A mechanical import-only cut candidate is therefore the line-1/line-11 pair in `WideTower`: import and open `AspisV8R15.ExactTowerBase`, while keeping `AspisWideTower.WideExact` and the rest of the exported `AspisWideTower` names. The old and new field definitions are textually equivalent after changing the namespace references. The remaining declaration gap below must be accounted for in any such patch; no patch or compile was made here.

## Exact field declarations consumed by `WideTower`

| `WideTower` use | Current declaration/source | Narrow counterpart | Inventory detail |
| --- | --- | --- | --- |
| `P`, `M31Exact`, `CM31Exact`, `qm31R`, `QM31Exact` | `AspisV5ComponentCQM31TowerExact`, `V5ComponentCQM31TowerExact.lean:42–132` | `AspisV8R15.ExactTowerBase`, `ExactTowerBase.lean:12–102` | Same literal/base/quadratic definitions under a different namespace. |
| M31 characteristic and primality | `m31PrimeFact` in the legacy tower, which makes the `CharP`/`ZMod` facts available to the cast proof | `m31PrimeFact` in `ExactTowerBase.lean:14` | Same class proposition, separately declared instance. `wideExact_natCast_ne_zero_of_pos_of_lt_characteristic` uses `CharP.cast_eq_zero_iff M31Exact P degree` at `WideTower.lean:83–86`; the rest of the proof uses `FaithfulSMul.algebraMap_injective` and `map_natCast` at lines 87–94. |
| Base non-square/rootless facts | `m31_neg_one_not_isSquare`, `cm31Rootless`, `cm31_qm31R_not_isSquare`, `qm31Rootless` in the legacy tower | Same declarations in `ExactTowerBase.lean:19–99` | These are the field hypotheses needed for the quadratic-algebra `Field` instances used by `WideTower`. |
| Norm of `qm31R` | `cm31_norm_qm31R` in the legacy tower | `ExactTowerBase.cm31_norm_qm31R`, lines 78–79 | Used through `cm31_qm31R_not_isSquare`; `WideTower` also uses `QuadraticAlgebra.norm_def` and norm multiplicativity. |
| Fintype instances on CM31 and QM31 | Global `cm31ExactFintype` and `qm31ExactFintype`, `V5ComponentCQM31TowerExact.lean:174–178`, each from `QuadraticAlgebra.equivProd` | No corresponding `Fintype` instance in `ExactTowerBase` | `WideTower.wideExactFintype` needs `Fintype QM31Exact` at line 69. |
| `qm31Exact_card : Fintype.card QM31Exact = P^4` | Legacy theorem at `V5ComponentCQM31TowerExact.lean:181–185` | No theorem of that name/content in `ExactTowerBase` | The legacy proof goes through `qm31ExactLimbEquiv` and `qm31Limbs_card`, a representation declaration imported from `V5ComponentCQM31Representation`. This is the exact cardinality edge that reintroduces the sampler/representation chain into the otherwise field-only tower. |
| A nearby cardinality proof | N/A | `AspisR19.TwoSwapFixedRootProbability.qm31_card`, `TwoSwapFixedRootProbability.lean:22–50` | This source uses local `Fintype` instances and quadratic-algebra product equivalences to prove `cm31_card`/`qm31_card`, but its imports start with `TwoSwapResidualNonzero` and `Mathlib.Algebra.MvPolynomial.SchwartzZippel`; it is not a standalone narrow field/cardinality module. It is a source-body analogue, not a narrow import substitute. |

`WideTower` itself uses the field-side declarations at these locations: `wideU` and the norm identity (`WideTower.lean:14–20`); `cm31I`, nonsquare arguments, and `wideRootless` (`23–60`); the `WideExact` abbreviation and field instance (`63–66`); the wide `Fintype` and degree-8 cardinality (`68–76`); the characteristic-cast theorem (`80–99`); and the QM31-to-wide algebra-map injection (`101–104`). Of those bodies, the missing narrow support declarations are specifically the CM31/QM31 finite instances and a `P^4` cardinality theorem. No other declaration from the V5 sampler/encoder representation appears by name in `WideTower`.

## Import-route and consumer inventory

The legacy route recorded in the earlier [`IMPORT-FOOTPRINT.md`](IMPORT-FOOTPRINT.md) includes:

```text
WideTower
  → AspisFormal.V5ComponentCQM31TowerExact
  → AspisFormal.V5ComponentCQM31Representation
  → AspisFormal.V5ComponentCBlockSamplerDirectHiding
     ├─→ AspisFormal.V5ComponentCRejectionSampler
     │   → AspisFormal.V5ComponentCSamplerKernel
     │   → AspisFormal.V5ComponentCEmatModel → import Mathlib
     └─→ AspisFormal.V5ComponentCConcreteDownstream
         → AspisFormal.V5ComponentCDirectHiding
            ├─→ AspisFormal.V5ComponentCSamplerKernel
            └─→ AspisFormal.V5ComponentCPreCProjectionMixed
                → AspisFormal.V5MixedFieldComposition
                → AspisFormal.CircleRectangularMasking → import Mathlib
```

The exact direct-import line from `V5ComponentCQM31TowerExact` to `V5ComponentCQM31Representation` is at `V5ComponentCQM31TowerExact.lean:1`. `Representation` directly imports `V5ComponentCBlockSamplerDirectHiding` and `Mathlib.FieldTheory.Finite.GaloisField`; the direct-hiding module imports both `V5ComponentCConcreteDownstream` and `V5ComponentCRejectionSampler`. `ConcreteDownstream` imports `V5ComponentCDirectHiding`; that module imports `V5ComponentCSamplerKernel` and `V5ComponentCPreCProjectionMixed`. `PreCProjectionMixed` imports `V5MixedFieldComposition`, which imports `CircleRectangularMasking`, whose line 1 is `import Mathlib`. The rejection-sampler branch reaches `V5ComponentCSamplerKernel` and `V5ComponentCEmatModel`, whose line 1 is also `import Mathlib`. Replacing the single `WideTower` import edge removes this legacy exact-tower dependency from that source consumer; it does not remove the old module from the repository or from separate legacy regression importers.

The complete direct importers of `WideTower` found under the V8 wide-reference source tree are:

| Direct importer | Other direct imports |
| --- | --- |
| `Wide/Instances.lean` | `Wide.Initial` |
| `Wide/JointList.lean` | `Wide.BatchSeparation`, `Wide.MultiplicityThreeGS`, `Wide.EncoderLinearity` |
| `Wide/SubfieldDescent.lean` | `Wide.EncoderConjugation`, `Mathlib.FieldTheory.Finite.GaloisField` |
| `R0/Fold.lean` | `Wide.FinalEncoder` |

These files refer to the stable `AspisWideTower.WideExact` surface. Recompiling them after a `WideTower` change is a source-consumer check; this inventory did not run it. Separate `Wide/EncoderRegression.lean` and `Wide/Regression.lean` explicitly `open AspisV5ComponentCQM31TowerExact` and have their own V7 regression imports; they are not direct `WideTower` importers and remain separate old-namespace consumers.

`R0.OpeningDefinitions` directly imports `R0.Chord`, `R0.FunctionalWeights`, `R0.ListsResponses`, and `R0.RootCounts`. Its `ListsResponses` edge imports `R0.Fold` and `Wide.JointList`, so the field cut is on one branch of its import closure. The prior footprint counts 127 repository modules and 48 explicit Mathlib imports across the four direct imports, including other unrelated `Mathlib` umbrella routes; this single edge removal does not establish that `OpeningDefinitions` will compile below 6 GiB.

`R0P.SemD3` itself directly imports `R0P.SemDecision`, `R0P.SemRounds`, and `R0P.SemClosed`; those source files do not directly import `WideTower` or `R0.OpeningDefinitions`. `R0P.SemD3Glue` consumes `AspisWideTower.WideExact` and imports `R0P.MessageDescent`; `MessageDescent` directly imports `Wide.SubfieldDescent`, which is a direct `WideTower` importer. Thus the same field edge lies in the SemD3 *glue* path, not in the direct imports printed by `SemD3.lean`. The unavailable `R0C.SemStatement` reported by the earlier attempt belongs to a separate source/cache issue: the available source `R0C/SemStatement.lean` directly imports `R0FS.V2`, not `WideTower`; this field cut alone does not resolve that missing object.

## Scope and remaining evidence

The previous import-footprint note reports the attempted `OpeningDefinitions` load hit Lean's 5,000 MB interpreter threshold at 6,209,616 KiB peak RSS with no swap. That observation is not a per-module memory attribution. It also records other umbrella `Mathlib` edges on the opening import cone. This inventory performs no resource measurement and does not claim the proposed edge replacement will fit the cap.

The companion source map records current SHA-256 hashes and direct imports for the old and narrow tower declarations, the exact-tower dependency route, `WideTower`, its four direct source importers, relevant OpeningDefinitions/SemD3 sources, and the nearby R19 cardinality proof. The map is pinned to the worktree HEAD above and should be refreshed if any listed file changes.
