# Current QM31 word-to-field reuse inventory

Read-only inventory for the next current-field arithmetic bridge. No Lean build or source edit was made. The source tree is `/Users/dominic/ZK/.worktrees/100bit-spend-path`.

## Smallest reusable pure tower closure

The old `AspisV8R17.QM31WordTower` is a pure word/residue/algebra module. Its direct imports are `QM31WordResidues` and `QuadraticTowerOperations`; that closure does **not** import the generated runtime modules or `UnsignedCoreSlice`. In particular, the namespace `GeneratedQM31Products` is defined as pure modular-word functions in `QM31WordFormulas`, and the tower module resolves those pure definitions through the residues import. The minimum local closure is five Lean files:

| Module | Direct local dependencies | Source SHA-256 |
|---|---|---|
| `AspisV8R17.RawReducerNat` | none | `1c65a462b3309e339750f518a1a37931b4c0595aa47cd04a830747b0d41f0101` |
| `AspisV8R17.QM31WordFormulas` | `RawReducerNat` | `d5cab0a52c5041e14d051497db164202e437b07c63299899c8afc180f04c2fcd` |
| `AspisV8R17.QM31WordResidues` | `QM31WordFormulas` | `8b2ec6d75bbbfde973c39f02f9b69c6cb1f7b432c9c2037e7f723df463e6acaf` |
| `AspisV8R17.QuadraticTowerOperations` | none | `48fe57215f6f386dd5101d4006f8d31969efebe5a6505eeda19c03b0589d8192` |
| `AspisV8R17.QM31WordTower` | `QM31WordResidues`, `QuadraticTowerOperations` | `66325008271913c8c589885ca3405e07e04b8ff75698996868b01e2cdd742b0a` |

All five files are under `docs/research/v8-full-view-zk-20260912/lean/AspisV8R17/`. The word formula, residue, and tower files were last changed in commit `5a3a6743f267f5356b2589f00978591afce85103`; `QuadraticTowerOperations` was introduced in `69f0f005f017ac5b5c0be0a31894fa941496dd39`.

The pure closure’s external imports are `Init.Data.Nat.Bitwise.Lemmas`, `Lean.Elab.Tactic.Omega`, `Mathlib.Data.Nat.Notation`, `Mathlib.Data.ZMod.Basic`, `Mathlib.Algebra.QuadraticAlgebra.Defs`, and `Mathlib.Tactic.Ring.Basic`. It does not need Aeneas. The compatible local Lean 4.31 backend/Mathlib cache is at `/Users/dominic/ZK/external/aeneas/aeneas-verif-workspace/aeneas/backends/lean/.lake` (backend repository commit `220c7ff9cce569dead1e72ef199775b3417493b7`, toolchain `leanprover/lean4:v4.31.0`); the six library boundary objects are present in the standard-library or sibling Mathlib cache. The searched 4.32 Aspis evidence caches have no objects for the four word/tower modules. `/tmp/aspis-r1-qm31-arithmetic-20261015/objects` contains only `AspisV8R17.RawReducerNat` from this closure. The R517 evidence retains a focused successful compile of unchanged `QuadraticTowerOperations` (exit 0, 1.00 s, RSS 1,192,084 KiB, swap 0) and its exact source pin, but does not retain its `.olean`.

## Exact reusable interfaces

`QM31WordFormulas.lean` lines 9–32 defines `WordPair := Nat × Nat`, coordinate `addWords`, `subWords`, `mulWords`, `rWords`, and composite `qmMulWords`, `qmSquareWords`, `qmAddWords`, and `qmSubWords`. `RawReducerNat.lean` line 12 supplies `P = 2147483647`.

`QM31WordResidues.lean` lines 11–16 defines `M := ZMod P`, `C := M × M`, `Q := C × C`, and `decodeC`/`decodeQ` by casting word coordinates. Its checked results are:

- `decode_add` (lines 18–21) and `decode_qm_add` (35–42), with no canonicality premise.
- `decode_sub` (28–33) requires `CanonicalPair y`; `decode_qm_sub` (43–50) requires both right-hand coordinate pairs canonical.
- `mul_canonical` (58–59) proves every `mulWords` output is canonical; `decode_mul` (61–70) identifies `mulWords` with the explicit complex-coordinate formula `cMul`.
- `decode_r` (72–79) needs a canonical pair.
- `decode_qm_mul` (90–99) identifies `decodeQ (qmMulWords x y)` with the explicit paired-coordinate `qMul`; `decode_qm_square` (101–109) does the same for `qSquare`. Neither theorem takes canonicality premises, since the intermediate multiplication outputs are canonical by `mul_canonical`.

`QuadraticTowerOperations.lean` lines 10–17 defines, for any `[CommRing F]`, `C F := QuadraticAlgebra F (-1) 0`, `r := ⟨2,1⟩`, and `Q F := QuadraticAlgebra (C F) r 0`, along with coordinate formulas `cmul`, `cr`. The theorems `cmul_eq` (19), `cr_eq` (22), `qmul_eq` (32), and `qsquare_eq` (39) equate those formulas to the corresponding actual quadratic-algebra multiplication, `r` multiplication, and square. Their only algebraic requirement is `[CommRing F]`; no nonresidue or field proof is needed.

`QM31WordTower.lean` lines 10–16 defines `M`, `C`, `Q`, `embedC`, `embedQ`, `decodeC`, and `decodeQ`; at lines 18–24 its `embed_product`/`embed_square` are definitional. Its exact operation-facing results are `decode_mul` (26–30), `decode_square` (32–36), `decode_add` (38–42), and `decode_sub` (44–49). `decode_mul` concludes `decodeQ (qmMulWords x y) = decodeQ x * decodeQ y`; `decode_sub` carries the same canonical-right-input premise as `decode_qm_sub`. The type `QM31WordTower.Q` has the same quadratic-algebra shape and `r = ⟨2,1⟩` as `ExactTowerBase.QM31Exact`, but no explicit cross-module equality theorem was located in this inventory.

## Current extracted operation-side API and gap

The current uncommitted `lean/ExtractedCurrentQM31Mul.lean` (SHA-256 `b071a9b498524f6ba800aafedbe1a86e5885ab0835bf99f58a55e13217282a54`) already defines matching word functions (`addWords`, `subWords`, `mulWords`, `rWords`, `qmMulWords`) at lines 13–36 and `wordsQM` at 41–43. `current_qm_mul_words` at lines 101–122 assumes `CanonicalQM x` and `CanonicalQM y`, then returns the actual extracted `field.QM31.mul` result, its canonicality, and exact equality of its four `.val` words with `qmMulWords`. It does not state that the word decoding equals multiplication in `QM31Exact`/`WideExact`. The imported current add-side theorem `ExtractedCurrentTowerAdd.current_qm_add_mod` at lines 59–74 yields coordinatewise modular addition and canonicality, but is likewise expressed as word values rather than exact-field decoding.

The old pure `QM31WordTower.decode_mul` is directly applicable to those same `qmMulWords` formulas after a typed bridge from `wordsQM` coordinates to `decodeQ`. No existing theorem was found that maps the current Aeneas `field.QM31`/`field.M31` representation into `QM31WordTower.Q`/`ExactTowerBase.QM31Exact`, or that carries the current operation theorems through such a map. The current exact tower imports retained in `evidence/lean-exact-base-projection-20261015/imports/` define `M31Exact = ZMod P`, `CM31Exact = QuadraticAlgebra M31Exact (-1) 0`, `QM31Exact = QuadraticAlgebra CM31Exact qm31R 0` (`ExactTowerBase.lean` lines 17, 62, 72–73, 102), and `WideExact = QuadraticAlgebra QM31Exact wideU 0` (`WideTower.lean` line 63; SHA-256 `4dfa22ed26400c6067917a25ff51f809554b852a69763c4c8f22959e221ab4fc`). Thus `WideExact` is an additional extension beyond the QM31 decoder target; no current-word-to-WideExact operation theorem was identified here.

The full `GeneratedQM31Tower` replay closure is larger and includes `UnsignedCoreSlice`; it should not be used as the import path for these pure formulas. The five-module closure above is the one that avoids the projected runtime declarations. This inventory records reusable statements only; it does not assert current Rust/Aeneas source correspondence or a completed current-field refinement.
