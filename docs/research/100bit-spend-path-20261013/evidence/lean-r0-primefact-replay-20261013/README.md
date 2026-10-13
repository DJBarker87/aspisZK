# R0 cached prime-instance replay

This records the bounded unchanged-source replay requested after
`OpeningDefinitions` encountered the stale
`AspisV5ComponentCQM31Representation.deployedPrimeFact` reference. All Lean
jobs used the pinned concrete-decoder runner with Lean 4.32.0, MemoryHigh=4G,
MemoryMax=6G, MemorySwapMax=0, TasksMax=128. Receipts, stdout, GNU time data,
and source hashes are preserved in `remote/`.

| Target / attempt | Result | Wall time | Peak RSS | Swap | Finding |
|---|---:|---:|---:|---:|---|
| `R0/Chord` a | failed | 2.91 s | 3,436,224 KiB | 0 | Unknown legacy prime Fact at `interpolationLinear`, `product_eval`, and `F6`. |
| `R0/PolynomialPair` a | passed | 2.22 s | 2,927,464 KiB | 0 | Unchanged direct predecessor rebuilt successfully; `liftLinear` has standard axioms. |
| `R0/Chord` b | failed | 2.91 s | 3,435,764 KiB | 0 | After the new `PolynomialPair` object was in the first object root, `interpolationLinear` passed; legacy Fact remained at `product_eval` and `F6`. |
| `R0/ChordImage` a | failed | 2.96 s | 3,532,800 KiB | 0 | Stopped earlier at max recursion depth while elaborating unchanged `pairWord_zero` at source line 34; later unknown identifier is cascading. |
| `R0/ChordImage` b | failed | 2.98 s | 3,533,064 KiB | 0 | Added only `set_option maxRecDepth 4096 in` before `pairWord_zero`; the same recursion-depth failure remains at its `rfl` proof. |
| `R0/ChordImage` c | passed | 3.14 s | 3,538,020 KiB | 0 | Replaced the large `rfl` reduction with `storedInitialCirclePoint20_child_zero` and explicit `simp only`; no option increase. Standard axioms. |
| `R0/Chord` c | passed | 3.18 s | 3,448,732 KiB | 0 | Replayed unchanged Chord after the rebuilt `PolynomialPair` and `ChordImage` objects. The former stale-prime references now elaborate. Standard axioms. |

The changed `PolynomialPair` cache resolves the legacy Fact at the linear-map
declaration in `Chord`, so the next owning cached module is `R0/ChordImage`.
Its unchanged source failed before that module's relevant declarations could be
replayed: `pairWord_zero` is currently a `rfl` proof and exceeded Lean's
recursion-depth setting. No option, statement, or proof change was made to
work around this. This is not an RSS failure; the job stayed below 3.6 GB. The
task is stopped at this diagnostic pending root review.

The source snapshots in `sources/` have hashes `ade2d0d7…2b01d189`
(`R0/Chord`), `0c1772aa…5e51099f` (`R0/PolynomialPair`),
`63dcc3d2…64f4dc06d` (`R0/ChordImage` attempt a),
`6e1e0f16…95746536` (`R0/ChordImage` attempt b), and
`227b30a3…0a1c6a0e` (`R0/ChordImage` attempt c). The `PolynomialPair`,
`ChordImage`, and `Chord` objects from passing focused compiles are archived
in `objects/`. Attempt b's local recursion-depth option did not resolve the
failure. Attempt c instead uses the existing symbolic child-zero domain
equality, avoiding reduction of the stored permutation definitions. No
resource cap increase was used. The source edit is confined to
`R0/ChordImage.pairWord_zero`; the theorem statement is unchanged.

The `Chord` attempt c log prints standard axioms for `F6`, `wideF6`,
`interpolationLinear`, and `product_eval` (`propext`, `Classical.choice`,
`Quot.sound`). The `ChordImage` attempt c log likewise prints standard
axioms for its four audited declarations. These are focused elaboration
results only; `OpeningDefinitions` has not yet been retried by this task.
