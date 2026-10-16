# Current mask linear forms and Horner caller

Six focused Lean 4.32 targets pass in the pinned NUC workspace. Their 19
axiom reports contain only `propext`, `Classical.choice` and `Quot.sound`.
All targets exit 0, all process swap counts are zero, maximum target
`/usr/bin/time` RSS is 2,999,948 KiB, and total controller wall time for the
six green attempts is 10.470 seconds. No unchanged full regression ran.

## What is checked

The actual extracted reverse loop consumes point cells 9 down to 0, updates
the suffix at every step, and adds that suffix to the weighted accumulator
only at nonzero indices. Its result equals the symbolic Nat recurrence.
The wrapper derives the zero seed and literal reverse range, then composes
the source's four scalar multiplications and two additions. Its two canonical
outputs decode to `3*suffix + 22*weighted` and
`275*suffix + 150*weighted`. Every point cell is explicitly required canonical.

The separate pure recurrence proof establishes that the zero-seeded ten-cell
model gives the two intended finite linear sums. It proves the suffix and
weighted moment invariants symbolically and handles index zero separately.
`maskLinear` is an exact body copy of historical `R0P.Mask.maskLinear`, with
its source hash recorded in the Lean file, but it is a different declaration.
There is no kernel equality to the historical declaration yet. A direct
composition from wrapper outputs to this local formula is also separate
from these six targets.

The Horner caller proof derives the actual prepared-multiplier constructor,
the coefficient-26 seed read, the reverse range and actual Horner loop
success. Its canonical result equals the degree-26 polynomial on decoded
coefficients. Canonical linear input and all 27 coefficient cells remain
explicit premises. This theorem does not establish how those cells were
populated.

## Reuse and rejected work

These targets reuse the checked array-read, reverse-range, scalar operation,
exact addition and Horner-loop/polynomial contracts. They use symbolic loop
induction, not concrete ten- or 26-step normalization. Production Rust and
generated function bodies are unchanged.

Eighteen failed attempts remain in the archive: four LinearStep, six
LinearLoop, five Linears and three LinearRecurrence attempts. Those are
excluded from the successful theorem set even where their failed axiom
reports contain `sorryAx`. The successful files have no such dependency.
Proof repairs concerned namespace/decoder aliases, induction parameters,
constant embeddings, finite-sum distribution and explicit index boundaries.

Before compiling the recurrence, root rejected a draft coefficient identity
that omitted `k != 0`: the identity is false at zero. The checked replacement
requires that premise and proves the zero case separately. Root also rejected
importing the broad cached historical semantic closure because some source
and receipt pins did not reconcile. The exact local formula keeps this pure
proof independent of that closure; the remaining declaration bridge is not
silently assumed.

## Evidence and limits

`manifest.json` records exact targets, source base revision, source/object
hashes, direct imports, command/controller pins, wall time, RSS, swaps,
axioms and all 24 attempt statuses. New sources are individually hash-pinned;
the receipt source-base revision remains
`b40d1cfffadbdf967f84cca23ea4e7f1553d564f`.
`proofs.tar.gz` contains 248 indexed files plus its summary. The independent
audit verifies every indexed archive entry, source snapshot and final object,
and reviews the explicit theorem premises and generated call flow.

Runs use the same pinned Lean 4.32 kernel/cache as the
[arithmetic port](../current-mask-lean432-20261016/README.md), one target at a
time with MemoryHigh=4G, MemoryMax=6G, MemorySwapMax=0, TasksMax=128,
Lean `-j1 -M5000` and a 300-second timeout. Import objects remain pinned in
that archive, the [loop/basis archive](../current-mask-loop-basis-20261016/README.md)
and the [power/basis archive](../current-mask-power-basis-20261016/README.md).

The generated declaration/source audit is extraction evidence, not a theorem
proving the Charon/Aeneas translation. Complete mask source correspondence,
actual acceptance, compiler/extraction, privacy, remaining soundness and
runtime/settlement release gates remain open. No new CU measurement or
complete 100-bit claim is made.

| Target | Wall seconds | Peak RSS KiB | Axiom reports |
|---|---:|---:|---:|
| ExtractedMaskLinearStep | 1.427 | 2987492 | 4 |
| ExtractedMaskLinearLoop | 1.707 | 2999948 | 1 |
| ExtractedMaskLinears | 1.851 | 2998876 | 4 |
| ExtractedMaskHornerCaller | 1.334 | 2991564 | 1 |
| ExtractedMaskLinearRecurrence | 1.454 | 1760760 | 7 |
| ExtractedMaskLinearMomentBridge | 2.697 | 2989552 | 2 |
