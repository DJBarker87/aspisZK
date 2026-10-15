# Exact basis, square/power and Horner polynomial evidence

Eight focused Lean 4.32 targets pass on the pinned NUC workspace. Their 21
axiom reports use only `propext`, `Classical.choice` and `Quot.sound`.
All exit 0, all process swap counts are zero, maximum target `/usr/bin/time`
RSS is 2,998,648 KiB and summed controller wall time is 11.352 seconds.
This batch extends the arithmetic and loop/basis checkpoints; it does not
repeat unchanged targets or a full manifest.

## Checked conclusions

- Actual CM31 squaring succeeds on canonical input and equals multiplication
  by itself. Its widened unsigned intermediate arithmetic has explicit bounds.
- Actual QM31 squaring succeeds with canonical output, first in retained word
  formulas and then as multiplication by itself in the exact field.
- Actual `state_only_hiding.mask_power_26` succeeds for every canonical input,
  returns a canonical output and decodes to the input raised to power 26.
  The proof follows the actual four squares and two multiplications.
- Actual tower-basis branches 0,1,2,3 decode to multiplication by `1`, `i`,
  `u`, `i*u` in the exact tower. Canonical input and coordinate<4 remain
  explicit premises. No representation equality between different tower
  carrier aliases is silently assumed.
- The actual reverse-Horner *model* seeded with coefficient 26 equals the
  degree-26 polynomial sum. A symbolic equality connects the generic
  recurrence to the model in the checked extracted-loop theorem. This
  result alone does not establish the caller's seed read, prepared
  constructor, coefficient population or complete mask result.

## Reuse and failed attempts

Pure modular proof bodies are reused from the retained
`GeneratedCM31SquareNormalized` and `GeneratedCM31Normalized` routes; their
old generated runtimes are not imported. The exact-square adapter reuses
`QM31WordTower.decode_square`. The basis interpretation reuses `sub_cast`,
`decode_r` and `cr_eq`, with small multiplication identities stated directly
in the exact tower carrier.

Fifteen failed attempts are retained separately: one pure square-arithmetic
attempt, one CM31-square bound attempt, one Horner-polynomial attempt,
three power adapter attempts and nine exact-basis attempts. Failure reports
may contain `sorryAx`; none contributes to the selected successful results.
The initial pure arithmetic draft used incomplete cast proofs and failed to
expose the fixed modulus; the replacement reused the retained integer normal
form directly. The widened square bounds needed only an explicit value for P.
Power adapter failures were decode aliases and redundant tactic steps.

The Horner specialization hit the unchanged 200,000-heartbeat limit while
trying to normalize a concrete range/power expression. It was replaced with
a named seed identity proved for arbitrary n, then instantiated at 26. The
replacement passes with the same cap; no concrete recurrence is unfolded and
no heartbeat limit is raised. Exact-basis failures involved representation
aliases and broad rewriting; the final proof uses direct exact-carrier
component identities and the retained CM31 residue map.

## Provenance and resources

Every target uses the existing controller/executor, one target at a time,
MemoryHigh=4G, MemoryMax=6G, MemorySwapMax=0, TasksMax=128, Lean `-j1 -M5000`
and a 300-second timeout. Source base is
`b40d1cfffadbdf967f84cca23ea4e7f1553d564f`; exact new-file hashes are recorded
per receipt. Generated Types/Funs and production Rust are unchanged.

`proofs.tar.gz` contains 209 hashed files plus its summary: all selected
source/object snapshots, every failed/successful attempt, raw logs, resource
receipts, direct-import pins and environment/controller history. Existing
objects are pinned in the [24-target arithmetic archive](../current-mask-lean432-20261016/README.md)
and [six-target loop/basis archive](../current-mask-loop-basis-20261016/README.md).
The Mathlib/Aeneas runtime cache remains the one pinned there. The archive
and per-file hashes were checked again after copying from the NUC.
`independent-audit.json` records a separate review of all indexed archive
files, selected source/object hashes, axiom reports and scoped claims.

These are exact arithmetic and model-composition results. Complete mask
source correspondence, actual verifier acceptance, compiler/extraction,
privacy, remaining soundness steps and runtime/settlement release gates
remain open. No new cost measurement or complete 100-bit claim is made.

| Target | Controller wall s | Peak time RSS KiB | Axiom reports |
|---|---:|---:|---:|
| ExtractedMaskSquareArithmetic | 0.696 | 949088 | 4 |
| ExtractedMaskCM31Square | 1.33 | 2610508 | 3 |
| ExtractedMaskCM31SquareEqMul | 1.199 | 2595564 | 1 |
| ExtractedMaskQM31Square | 1.318 | 2602116 | 1 |
| ExtractedMaskQM31SquareExact | 1.383 | 2979792 | 1 |
| ExtractedMaskPower26 | 1.837 | 2993044 | 1 |
| ExtractedMaskTowerBasisExact | 2.024 | 2998648 | 5 |
| ExtractedMaskHornerPolynomial | 1.565 | 2997148 | 5 |
