# Direct source consumers and extraction comparison

Read-only inventory at base worktree commit `0dbaf0c8d576a8da71e031b89cef2c9083c67cca`.
“Direct consumer” below means the source file contains an explicit reference to
one of the moved declarations; some files obtain it through an intermediate
R0 or semantic import rather than importing `R0.Dot`/`R0.OpeningWeights`
themselves. This records source dependencies, not build success or semantic
validity.

## Semantic and parser-facing references

| Source file | References in source | Import path shown in file |
|---|---|---|
| `docs/research/v8-r0-sem-20261007/lean/R0S/SemStatement.lean` | `eqWeight`, `AspisR0.RoundNormalization.dot` (lines 92, 229) | `R0.OpeningDefinitions` |
| `docs/research/v8-r0-sem-proof-20261008/lean/R0P/SemView.lean` | `coeffWeight`, `dot_coeffWeight_left`, RoundNormalization `dot` (lines 78–79) | `R0P.SemSource`, `R0P.Copy` |
| `docs/research/v8-r0-sem-proof-20261008/lean/R0P/SemDecision.lean` | `eqWeight` in `selAt` (lines 67–68) | `R0P.SemView`, `R0P.LaneMap` |
| `docs/research/v8-r0-sem-proof-20261008/lean/R0P/SemD3.lean` | `eqWeight` in `SemD3` (line 30) | `R0P.SemDecision`, `R0P.SemRounds`, `R0P.SemClosed` |
| `docs/research/v8-r0-sem-proof-20261008/lean/R0P/SemHonest.lean` | unfolds/reconciles `eqWeight` (lines 41, 163) | `R0P.SemD3` |
| `docs/research/v8-r0-sem-proof-20261008/lean/R0P/SemD3Glue.lean` | `coeffWeight`, `eqWeight`, RoundNormalization `dot` (lines 931–936) | semantic/glue imports including `R0FS.Hypotheses` |
| `docs/research/v8-r0-sem-proof-20261008/lean/R0P/SemDeg.lean` | unfolds `eqWeight` through the `selAt` selector (line 241) | `R0P.SemD3`, `Mathlib.Order.Interval.Finset.Fin` |
| `docs/research/v8-r0-sem-proof-20261008/lean/R0P/MaskProtocol.lean` | RoundNormalization `dot` in Libra row pairing (line 46) | `R0P.SemD3Glue` |
| `docs/research/v8-r0-sem-proof-20261008/lean/R0P/MaskValue.lean` | unfolds RoundNormalization `dot` for Libra pairing (lines 102–103, 145) | `R0P.SemDeg` |
| `docs/research/v8-r0-sem-proof-20261008/lean/R0P/MaskD3Glue.lean` | `coeffWeight`, `eqWeight`, RoundNormalization `dot` (lines 61–66) | `R0P.MaskEarly`, `R0P.MaskNoHit` |
| `docs/research/v8-r0-zk-20261009/lean/R0Z/Shift.lean` | RoundNormalization `dot` in shifted Libra claims (line 334) | `R0Z.D12`, `R0Z.GoodDensity`, `R0Z.LawTransport` |
| `docs/research/v8-r0-zk-20261009/lean/R0Z/HonestView.lean` | `eqWeight`, unfolds RoundNormalization `dot` (lines 72, 93) | `R0Z.ViewAffine` |
| `docs/research/v8-r0-fs-20261006/lean/R0FS/Protocol.lean` | `coeffWeight`, `eqWeight`, and the opening dot in point-claim premise (line 75) | `R0.Binding`, `R0.Ledger`, `R0.QueryLaw`, `FS.Theorem`, `R0FS.Verifier` |
| `docs/research/100bit-spend-path-20261013/lean/D18OpeningWeights.lean` | `coeffWeight`, `eqWeight`, indicator, moved dot and two reindexing theorems | `R0.OpeningWeights`, `R1D18PointWeights`, `Lean.Elab.Tactic.Omega` |
| `docs/research/100bit-spend-path-20261013/lean/SemanticOpening.lean` | `coeffWeight`, `eqWeight`, moved dot in its row map and witness claim (lines 25, 36, 47–50, 70–71) | `R1CandidateDescent`, `R1RawOpening`, `R1D18OpeningWeights` |

## R0 algebra and proof consumers

The pre-existing R0 proof layer also refers directly to the moved names:

| Source file | References | Import path |
|---|---|---|
| `docs/research/v8-wide-reference-20261005/lean/R0/OpeningDefinitions.lean` | Uses `coeffWeight`, `eqWeight`, `indicator`, and `dot` in remaining data/defect/weight definitions (lines 44, 55, 58–59) | `R0.Chord`, `R0.FunctionalWeights`, `R0.ListsResponses`, `R0.RootCounts`, now `R0.OpeningWeights` |
| `docs/research/v8-wide-reference-20261005/lean/R0/OpeningAlgebra.lean` | Point and batched pairing use `coeffWeight`, `eqWeight`, `dot` (line 46 and following algebra) | `R0.OpeningDefinitions` |
| `docs/research/v8-wide-reference-20261005/lean/R0/Binding.lean` | Opening-claim condition and inactive-indicator rewrite use moved weights/theorem (lines 131, 176) | `R0.BadSetBounds`, `R0.OpeningAlgebra`, `R0.FibreRestoration`, `Wide.SubfieldDescent` |
| `docs/research/v8-wide-reference-20261005/lean/R0/BadSetBounds.lean` | Uses the moved `dot` in `qWeights` equalities (lines 160, 181, 206) | `R0.OpeningDefinitions` |
| `docs/research/v8-wide-reference-20261005/lean/R0/Round.lean` | Uses moved `dot` for round-evaluation and boundary formulas | `R0.RoundNormalization`, `R0.RoundCore` |
| `docs/research/v8-wide-reference-20261005/lean/R0/Chord.lean`, `R0/ChordImage.lean` | Use moved `dot` in chord/image pairing lemmas | `R0.ChordImage`/`R0.Round` dependency chain; both open `AspisR0.RoundNormalization` |

The other `dot` in `R0/FunctionalWeights.lean` resolves to
`AspisR0.LinearDual.dot`, not the extracted RoundNormalization definition;
it is not counted as a consumer of `R0.Dot`.

## Byte comparison and surrounding context

The removed declaration region from the original `OpeningDefinitions.lean`
(starting at its Boolean-weight doc comment and ending immediately before
`def interpolants`) is byte-for-byte identical to the corresponding region in
`R0/OpeningWeights.lean`: both are 1,647 bytes, SHA-256
`206132f94142db00078d342deae8cafad67d55c74a1f7c43b49e77cfcbc3b146`.
This includes all declaration comments, signatures, proof bodies, and spacing.

The original RoundNormalization declaration line
`def dot {n : Nat} (q w : Fin n → K) : K := ∑ i, q i * w i` occurs byte-for-byte
in `R0/Dot.lean`; its line SHA-256 is
`c0ad29e14be0c5c8614afb60038c41870e111a886092159e73145b593ef0d6c6`.

Only the surrounding headers/contexts differ. `R0.Dot` replaces the original
`R0.Fold`/polynomial/R0/V5 opens with explicit big-operator, field, finite-Fin,
and `AlgorithmicCircleDecoderV7` imports; it retains the original namespace,
section typeclass context, and dot line. `R0.OpeningWeights` imports `R0.Dot`
and `Wide.InitialEncoder`, retaining the original namespace and exact section
variable context. It keeps only the opens needed by the moved block
(`AspisPool.AlgorithmicCircleDecoderV7`, `AspisWide.InitialEncoder`,
`AspisR0.RoundNormalization`, scoped big operators); the remaining broad opens
from `OpeningDefinitions` stay in that module. `OpeningDefinitions` and
`RoundNormalization` each gained one import and lost only their extracted
definition block. No declaration in either historical dependent file was
otherwise rewritten in this extraction.
