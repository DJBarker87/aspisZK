# Extracted reverse Horner loop and basis-operation evidence

Six new selected-mask source helpers pass on the same pinned Lean 4.32 kernel
and NUC cache as the [arithmetic port](../current-mask-lean432-20261016/README.md).
There are 13 axiom reports, all restricted to `propext`, `Classical.choice`,
and `Quot.sound`. All six targets exit 0; maximum target `/usr/bin/time` RSS
is 2,994,944 KiB and all process swap counts are 0. Each runs alone under
MemoryHigh=4G, MemoryMax=6G, MemorySwapMax=0, TasksMax=128, with no outer flock,
no dependency build and no full-manifest replay.

`body_loop2_model` proves execution of the actual extracted reverse Horner
loop matches a symbolic Nat recurrence. It requires start=0, end=n, n<=27,
canonical input linear/shared values and every coefficient, plus the explicit
`PreparedFor` invariant. One step performs prepared multiplication then adds
the selected coefficient, preserving canonicality. Induction handles arbitrary
permitted n without expanding a concrete 26-step recurrence. The extracted
caller uses n=26 and seeds shared with coefficient 26. Establishing that caller's
array read, range construction and all input hypotheses is still separate.

`current_mul_tower_basis_words` proves each of the four actual source branches
succeeds on canonical input with coordinate<4, returns canonical output and
matches the explicit word map. Negation's zero/nonzero behavior and the CM31
i/r operations are checked along the way. This is not yet the exact-field
basis interpretation or coefficient-array population proof.

## Reuse, failures and pins

The reverse-range helper follows the retained R306 iterator facts; the array
read follows the R616 pattern; the whole-loop induction follows the R311
pattern. They import the actual generated Aeneas functions and checked current
operation adapters. The prior pure field module reuse and constructor-derived
PreparedFor invariant are recorded in the arithmetic bundle. No old projected
runtime is imported as if it were current source.

Five failed Lean attempts are retained: HornerStep a (decode alias rewrite),
HornerLoop a (ambiguous name and fixed induction parameters), HornerLoop b
(local index alias rewrite), Neg a (scalar-subtraction notation), and TowerBasis a
(word-pair rewrite). Their failure reports contain `sorryAx` and are explicitly
excluded from the successful theorem set. Fixes preserve the reviewed statements.
A preflight review also rejected an earlier recurrence definition constructing
Fin 27 from an unbounded Nat; the checked model instead uses Nat indices with
zero outside the array, and the execution theorem proves every accessed index
is in range. The old uncompiled draft remains in the prior source kit.

The source base remains `b40d1cfffadbdf967f84cca23ea4e7f1553d564f`; these new
source files are individually pinned by successful attempt hashes. Generated
Funs is `4aa955ab74e6db926d02bdbee7dd9cdf5f755b019311dd3c67599bd8d97aa395`.
The archive contains all six final sources/objects, failed and successful
snapshots, raw logs, resource receipts, environment pins and controller. Its
direct-import pins refer to objects in the prior 24-target archive
(SHA256 `45243b7b979bf76dd0e6d5bbfa1e71423fb8d9ad46c045760833b795583240c0`)
and pinned Aeneas/Mathlib cache. No production Rust changed.

`manifest.json` contains exact target, exit, timing, RSS, swap, revision,
source/import/object hashes and axiom reports. `independent-audit.json` checks
all six current sources against green snapshots and the actual caller shape.
Whole-mask correctness, accepted-verifier correspondence, compiler/extraction,
privacy and the remaining soundness/runtime gates remain open.

| Target | Controller wall s | Peak time RSS KiB | Axiom reports |
|---|---:|---:|---:|
| ExtractedMaskReverseRange | 1.302 | 2610700 | 3 |
| ExtractedMaskHornerStep | 1.368 | 2988848 | 3 |
| ExtractedMaskHornerLoop | 1.498 | 2994944 | 1 |
| ExtractedMaskNeg | 1.243 | 2606464 | 2 |
| ExtractedMaskBasisComponents | 1.209 | 2595124 | 3 |
| ExtractedMaskTowerBasis | 1.241 | 2601360 | 1 |
