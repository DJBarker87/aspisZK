# Exact tower import refactor evidence

This focused run checks the mechanical extraction of finite-set facts from
`WideTower` onto the existing `AspisV8R15.ExactTowerBase` field definitions.
No field definition, theorem premise, or `WideExact` construction was changed.

## Source changes

- `lean/AspisV8R15/ExactTowerFinite.lean` adds only the CM31/QM31 finite
  instances and cardinality results, using `QuadraticAlgebra.equivProd`,
  `Fintype.card_prod`, `ZMod.card`, and `pow_add`.
- `lean/WideTower.lean` changes only the import and namespace openings. Its
  declarations and proof bodies remain unchanged.
- `Wide/Cardinality.lean` adds a direct import for the concrete Fin enumeration
  retained in cached decoder interfaces. `Wide/JointList.lean` imports that
  existing cardinality module directly. These are import-only changes; theorem
  statements and proof bodies are unchanged.
- Source snapshots and hashes are under `sources/`; the compiled
  `ExactTowerBase` dependency has the same source SHA as the worktree source
  (`04cc8994…5517ffd5`). Its reused object SHA is
  `30c15724…32ea486e` and was linked from the pinned generic cache into the
  concrete runner's first namespace root so Lean could resolve the module.

## Focused compiler results

Runner: `/home/dombarker/project-offloads/aspis-r1-concrete-decoder-20261013/compile-one.sh`,
Lean 4.32.0, each attempt in its own user scope with MemoryHigh=4G,
MemoryMax=6G, MemorySwapMax=0, TasksMax=128. Full runner receipts, logs, and
GNU time records are in `remote/`.

| Target / attempt | Result | Wall time | Max RSS | Swap | Note |
|---|---:|---:|---:|---:|---|
| `AspisV8R15/ExactTowerFinite` a | failed | 0.10 s | 189,380 KiB | 0 | Missing object in first namespace root; no source elaboration. |
| `AspisV8R15/ExactTowerFinite` b | failed | 0.98 s | 2,431,800 KiB | 0 | Initial CM31 `pow_add` rewrite did not match `P * P`. |
| `AspisV8R15/ExactTowerFinite` c | failed | 0.98 s | 2,430,200 KiB | 0 | Extra `rfl` after the preceding rewrite had already closed the goal. |
| `AspisV8R15/ExactTowerFinite` d | passed | 1.03 s | 2,442,792 KiB | 0 | Both cardinality theorems report `[propext, Classical.choice, Quot.sound]`. |
| `WideTower` a | passed | 2.07 s | 2,460,308 KiB | 0 | All five existing audited declarations report standard axioms only. |
| `Wide/Instances` a | failed | 1.44 s | 2,997,440 KiB | 0 | Existing exact V7 declarations hit unknown SimplexCategory instance constant. |
| `Wide/JointList` b | failed | 1.55 s | 2,871,240 KiB | 0 | Same unknown constant in the cached dependency closure. |
| `R0/Fold` a | passed | 1.80 s | 2,929,468 KiB | 0 | `wideF4` reports `[propext, Classical.choice, Quot.sound]`. |

The failed consumer logs contain `sorryAx` in declarations emitted after the
elaboration error; those attempts are failures, not theorem evidence. The two
consumer failures report `SimplexCategory.instFintypeToTypeOrderHomFinHAddNatLenOfNat`.
Its source declaration is Mathlib
`Mathlib/AlgebraicTopology/SimplexCategory/Basic.lean:596` (source SHA
`5a1c533c…b1c5cc5`). The compiled Mathlib object SHA is
`ca86c814…26cecdb`. `Wide/Cardinality.lean` explicitly documents that its
full import environment may select a SimplexCategory enumeration for concrete
`Fin` dimensions. The exact V7 declaration owners are `Wide/Initial.lean`
(`AspisWide.Terminal.exactV7InitialWidth29CurveDecodable`, source SHA
`7e74ef9f…c7ea509`) and `Wide/Terminal.lean`
(`exactV7FinalDegreeThreeCurveDecodable`, source SHA
`943d9b78…bb26b0daf`); the corresponding cached source hashes match these
worktree sources. Subsequent successful import repairs are recorded below.

`Wide/SubfieldDescent` was not compiled here; root has separately refactored
it through `Wide/SubfieldDescentCore` and owns its wrapper check. No package
build or manifest replay was run.

## Explicit Fin-instance dependency repair

Root's `R1FinInstanceDiagnostic` source imports
`Mathlib.AlgebraicTopology.SimplexCategory.Basic`, checks the exact missing
instance name, and compiles it successfully at 1.84 GB RSS. Following that
diagnostic, `Wide/Cardinality.lean` gained that one direct import plus a short
comment documenting the retained finite enumeration and the existing
instance-abstracting cardinality theorem. No declarations or proof bodies in
that module changed.

| Target / attempt | Result | Wall time | Max RSS | Swap | Note |
|---|---:|---:|---:|---:|---|
| `R1FinInstanceDiagnostic` a | passed | 0.75 s | 1,835,608 KiB | 0 | Exact instance declaration resolved; standard axioms. |
| `Wide/Cardinality` b | passed | 0.76 s | 1,843,288 KiB | 0 | Updated direct import; standard axioms. |
| `Wide/Instances` b | passed | 1.53 s | 3,140,828 KiB | 0 | Previous missing-instance failure cleared; all three emitted declarations have no `sorryAx`. |
| `Wide/JointList` c | failed | 1.63 s | 2,870,996 KiB | 0 | Same unknown constant remains at source lines 19 and 71 even with updated `Wide/Cardinality` output present in the concrete runner's first object root. Stopped without adding another import. |
| `Wide/JointList` d | passed | 1.66 s | 3,014,680 KiB | 0 | Root-authorized direct `import Wide.Cardinality`; all five emitted declarations report standard axioms. |

The root runner source/object for the diagnostic and the updated
`Wide/Cardinality` output object are preserved under `sources/` and
`objects/`; their hashes and full resource receipts are included. The second
`Wide/JointList` failure cleared after adding its direct `Wide.Cardinality`
import. No declaration, theorem statement, or proof body changed.
