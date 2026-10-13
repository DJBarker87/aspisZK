# `R0.OpeningDefinitions` import-footprint inventory

This is a read-only source/cache inventory. I did not invoke Lean, alter the runner, or change any Lean source while preparing it. The motivating measurement is attempt `b` in `R1D18OpeningWeights-b.receipt.json`: the file had no `R0P.SemView` import, but loading `R0.OpeningDefinitions` still terminated at the runner's 5,000 MB interpreter threshold, with 6,209,616 KiB peak RSS, in 2.97 seconds and zero swap. The output reports only an interpreter memory exception, so the footprint below identifies plausible broad-import contributors, not a per-module causal RSS attribution.

## Source and cache graph

The source file `docs/research/v8-wide-reference-20261005/lean/R0/OpeningDefinitions.lean` has four direct imports:

- `R0.Chord`
- `R0.FunctionalWeights`
- `R0.ListsResponses`
- `R0.RootCounts`

Walking those imports through the available V8 wide-reference and `AspisFormal` sources reaches 127 repository modules and 48 distinct explicit `Mathlib.*` import names. This excludes Mathlib's own transitive graph. The import route expands especially through `ListsResponses → Fold → WideTower` and `ListsResponses → Wide.JointList → Wide.MultiplicityThreeGS / Wide.EncoderLinearity`; `Chord` also reaches `ChordImage → Round → RoundCore`.

Broad umbrella imports found on the reachable paths are:

- `Mathlib.Tactic` in `R0.RootCounts`, `R0.ResponseSelection`, `R0.LinearDual`, `R0.ChordGeometry`, `R0.RoundCore`, and `R0.ChordDegree`.
- `Mathlib` in `AspisFormal.V5ComponentCEmatModel`, `CoreHidingPMF`, `CoreHiding`, `CircleRectangularMasking`, `CircleDiscreteAvailability`, `CircleTensorBinding`, `CircleTMatrixHiding`, `MaskingHiding`, `CircleVandermondeGeneral`, `CircleVandermonde`, `CirclePointLiveness`, and `V5ComponentBTriangularHiding`.

The large path is not just tactic imports: `WideTower → AspisFormal.V5ComponentCQM31TowerExact → V5ComponentCQM31Representation → V5ComponentCBlockSamplerDirectHiding → V5ComponentCRejectionSampler → V5ComponentCSamplerKernel → V5ComponentCEmatModel` reaches an `import Mathlib`. A sibling path through `V5ComponentCConcreteDownstream`, `V5ComponentCDirectHiding`, and `V5ComponentCPreCProjectionMixed` reaches `CircleRectangularMasking` and further umbrella-Mathlib modules. Thus importing `OpeningDefinitions` loads an opening-weight file whose own declarations need only a small fragment, but whose imports expose substantial unrelated proof environments.

At the pinned runner, `R0/OpeningDefinitions.olean` is a 380,800-byte symlink into `aspis-fs-generic-20261006/R0-oleans-from-mac`; direct import object sizes are small (Chord 580,272 bytes; FunctionalWeights 105,480; ListsResponses 248,296; RootCounts 60,120). These sizes do not measure the transitive environment loaded. The reachable cached object for `AspisFormal/V5ComponentCQM31TowerExact` is 10,357,128 bytes and symlinks into the older ZK-v7 build; several other reached modules likewise resolve to that older build. The runner therefore has a mixed-origin cache graph, with no single local source tree corresponding to all cached imports.

## Small extraction candidate

A standalone `R0.OpeningWeights` (name is a candidate) can own the existing constants in namespace `AspisR0.Opening` without duplicating them: `eqWeight`, `indicator`, `coeffWeight`, their existing linearity/sum lemmas, `dot_coeffWeight_left`, and `dot_coeffWeight_indicator` can be moved there, and `OpeningDefinitions` can import that module and delete its copies. `InitialMessage K` is the reducible alias `Fin 1024 → K` (source: `AspisFormal/AspisFormal/Pool/AlgorithmicCircleDecoderV7.lean:23`); the moved declarations can use that function type directly, preserving definitional equality without importing the `AspisFormal.Pool` module solely to name the alias. Their mathematical ingredients are finite products/sums, a field, `Finset`, and finite equivalence reindexing.

The dot lemma currently states its result using `AspisR0.RoundNormalization.dot`, whose definition is in `R0.RoundNormalization` and whose source imports `R0.Fold`. To expose the exact existing dot theorem from the small module, the no-duplication route is to move the `RoundNormalization.dot` definition into the small module under its current fully qualified name, then have `RoundNormalization` consume it instead of redefining it; move `Opening.dot_coeffWeight_left` and `Opening.dot_coeffWeight_indicator` alongside the weight definitions. This keeps the names and theorem statements while making the proposed import independent of `RoundNormalization`'s `Fold` cone. It requires editing/refactoring existing source, which is outside this inventory task. An alternate minimal core that keeps `RoundNormalization` unchanged can prove a raw finite-sum reindex theorem, but it will not let D18 directly invoke the existing `Opening.dot_coeffWeight_left` without importing `OpeningDefinitions` again.

A plausible minimal explicit import set to test for the extracted core is `Mathlib.Algebra.BigOperators.Fin` plus `Mathlib.Algebra.Field.Basic` (and only add `Mathlib.Data.Finset.Basic` if those do not provide the used Finset API in the pinned Mathlib). The declarations use no tactic-heavy proof: `dot_coeffWeight_left` is a finite-equivalence sum reindex, and the indicator dot lemma reduces with a filter/sum identity. This candidate import set is reasoned from declaration use, not compiled or validated here.

## Focused dependency checks after any approved extraction

The source importers found in the available repository are `R0.OpeningAlgebra`, `R0.BadSetBounds`, `R0S.SemStatement`, and this task's `D18OpeningWeights.lean`. `R0.Round` directly imports `R0.RoundNormalization`. For a move of `RoundNormalization.dot`, the mechanical focused sequence is the new weight core, `R0.RoundNormalization`, `R0.OpeningDefinitions`, then those four direct opening-definition importers and `R0.Round`; compile any changed generic theorem first, and do not infer that this sequence will fit the existing runner threshold. `R0.RoundNormalization` itself still imports `R0.Fold`, so its own recompile may retain the WideTower cone. A source split that removes the need for D18 to import `OpeningDefinitions` is the main direct benefit; the wider existing opening module and its consumers remain broad.

## Manually checked proof orientation

`D18Transport.lean` says `row_involutive j : row (row j) = j`, and `rowEquiv` uses `row` for both inverse laws. In `D18OpeningWeights.lean`, after `apply rowEquiv.injective` and rewriting `rowEquiv.apply_symm_apply`, the remaining goal is `j = row (row j)`. The current final line `exact row_involutive j` has the opposite orientation. It should be `(row_involutive j).symm` (or an equivalent symmetric rewrite). This is a source-level check only; the file did not reach elaboration in either attempt.

## Source hashes used

SHA-256 values identify the inspected source revisions, not the cached `.olean` contents.

| Source | SHA-256 |
| --- | --- |
| `docs/research/v8-wide-reference-20261005/lean/R0/OpeningDefinitions.lean` | `397f9d73b203b1f464df0c8a04a30f79bc92c82fe5e3b2c55a130a3f2990d400` |
| `.../R0/Chord.lean` | `ade2d0d7ccbaa66cac517578e8c4ead02b674d81fb1e2f1638f3746c2b01d189` |
| `.../R0/ChordImage.lean` | `63dcc3d21f38eb7f83649a4a2691998e3200c64f8e8ccc33110233364f4dc06d` |
| `.../R0/ChordGeometry.lean` | `1fe7c50563c7da85dad935fd4aa1567debd785e2488c8138290fcce3e72819e6` |
| `.../R0/ChordDegree.lean` | `3cdb65a53141e834b422b4e17ffeec20e6069682c23d7fe2e0eeaca2b9683248` |
| `.../R0/FunctionalWeights.lean` | `d5387a5ffe8a6ba824312fff112d7cb998a68e38cd1a36b8acdd79bebd9f96d0` |
| `.../R0/LinearDual.lean` | `f6e20b5694301d4fe0c82a0ef03aa7605576de49af5b94bc439892d4d4c59388` |
| `.../R0/ListsResponses.lean` | `cd96f9fd4c3ee6fdfc5882b9b09e00004d8f2320e8f40f7b38e7cbce0c3a2902` |
| `.../R0/Fold.lean` | `fab2b0dc3cf0e32dd414e6737660d208989e2b8eb4ecd35eeb23354cd0e93329` |
| `.../R0/ResponseSelection.lean` | `4a9b5979019924b6cc538480ec06b802d4eac1bd14ba5a098890bc5a346075fd` |
| `.../R0/RootCounts.lean` | `e24d2db97d260aef358874644030f4b8e18b34e86b1eeb31b2a94583386ab42c` |
| `.../R0/Round.lean` | `ac4c9c948dc832a1abb54ce73ac3889e169b8ca4a144e3722986141cb40f33e8` |
| `.../R0/RoundNormalization.lean` | `de099073bffc2c73d24b161213d286ab66d80fc8649f0199fdc07ece7dbcb60a` |
| `.../Wide/JointList.lean` | `762657e7cb378837efb33304ad5bfbc4849a152fe19358e8eb706edcdf894066` |
| `.../Wide/MatchedInstances.lean` | `6e9e16b392db18fe60d8f9fa3abbf11f0472c698d3f1f3fb7033933d8babb376` |
| `.../WideTower.lean` | `f55bd736f0e8bb3fedda8c862bf8311fe3be609b17b72a01f0e476b33c34c538` |
| `AspisFormal/AspisFormal/Pool/AlgorithmicCircleDecoderV7.lean` | `2faaf875cf3237c9409a19bf2bbb2dd3d302288ed24b059aabb90fac5ddd6471` |
| `AspisFormal/AspisFormal/V5ComponentCQM31TowerExact.lean` | `75404d16b5a71f67146b91ca35739b111f81bb730beb77432267f2b5385cebe5` |
| `AspisFormal/AspisFormal/V5ComponentCEmatModel.lean` | `0434d25710ce10f665f922d4bf50dce443c798586da66b964bcf62d2dce492c4` |
| `docs/research/100bit-spend-path-20261013/lean/D18Transport.lean` | `ffa944f42b5188e89d6a538a5fe345e4347a148dcc080feb01673c82b6099033` |
| `docs/research/100bit-spend-path-20261013/lean/D18OpeningWeights.lean` | `6951e940ebd5cf016b0ea8ddf1be34acfb2b306dd73eb07f5785ce74f1d0eac1` |

The reachable sources with an exact `import Mathlib` umbrella are also pinned here:

| Source | SHA-256 |
| --- | --- |
| `AspisFormal/AspisFormal/CoreHidingPMF.lean` | `6022a1c92aafdcb505a05c1b1eecd73f7a1d84edf2c7f8a9a09671b5544226b9` |
| `AspisFormal/AspisFormal/CoreHiding.lean` | `1e08b5ee518708b3572969400900ff9752ec9170682be0f6e6eb86b93a050e09` |
| `AspisFormal/AspisFormal/V5ComponentCEmatModel.lean` | `0434d25710ce10f665f922d4bf50dce443c798586da66b964bcf62d2dce492c4` |
| `AspisFormal/AspisFormal/CircleRectangularMasking.lean` | `001d880f10b8a55a7aa74930f8e7e46214d57a96603df34e748e0de1dbd60d04` |
| `AspisFormal/AspisFormal/CircleDiscreteAvailability.lean` | `bf82e5c4cf56f1e222cd474adc9b30ff9d0664a0e38e42ca7045378b7d6bddc1` |
| `AspisFormal/AspisFormal/CircleTensorBinding.lean` | `2a43848cb77653442980892544f14385ac568c6395fdd56da4c847711ced2ba1` |
| `AspisFormal/AspisFormal/CircleTMatrixHiding.lean` | `e7347a146606367d5c465550e8636a180686435c3c50574cd94cff7fcdf1892a` |
| `AspisFormal/AspisFormal/MaskingHiding.lean` | `871ec1633ea5cfe08893d63e8dcfa52cf2aef17d11deb56b0c14e883e73d2d8b` |
| `AspisFormal/AspisFormal/CircleVandermondeGeneral.lean` | `06ab422d928b1210c7511d35d4f484d6df3cc6f3508cf5fee443fc304076de50` |
| `AspisFormal/AspisFormal/CircleVandermonde.lean` | `b5c7ed9428321ee0e989d057bf6109056941ac15eca02a7b6b9ff3211e74bd87` |
| `AspisFormal/AspisFormal/CirclePointLiveness.lean` | `829cf31a4a9aa50576f8750437e39440523e0f3ac60f174218d2634c1ba78ae7` |
| `AspisFormal/AspisFormal/V5ComponentBTriangularHiding.lean` | `9fabd2434c5ada34552e1f61288ac2c94a3db6b7a5d54df66facde72a1a8da94` |
