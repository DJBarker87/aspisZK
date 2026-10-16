# Complete extracted mask formula

Fifteen focused targets pass on the pinned Lean 4.32 NUC workspace. The final
theorem, `current_selected_mask_value_scheduled`, proves that the actual
extracted selected-mask caller succeeds, returns a canonical field value,
and equals the intended local exact mask formula. Its premises are canonicality
of the 16 C1 inputs, 10 mask-only inputs, 10 point coordinates and explicit
mask `g`. All intermediate call successes, bounds and canonicality are derived.

## Checked scope

The two source loops populate the degree-26 coefficient array at their exact
table destinations, multiplying each input by the literal tower basis element
selected by its column modulo four. Their schedules are injective, disjoint,
and cover every coefficient except index 23. That index remains zero.
Symbolic loop invariants prove which cells have been written and which cells
are preserved. A finite equivalence reindexes the polynomial without expanding
all its cells. The full caller composes those facts with the existing linear
forms, prepared Horner evaluator, power-26 routine and final arithmetic.

Writing `L0` and `L16` for the two checked local linear forms, the result is
the sum of the 16 scheduled C1 terms and 10 scheduled mask-only terms at `L0`,
plus `(1 + L16^26) * g`. `LinearMap` also proves that the local linear formula
commutes with a ring homomorphism. The concrete transport into the historical
`WideExact`/`R0P.Mask.maskValue` declaration remains separate.

The batch reuses the preceding arithmetic, exact basis, power, reverse Horner,
array, iterator and weighted-moment proofs. Rust and generated function bodies
are unchanged. The generated-source pins associate these declarations with
the selected Rust source; they are not a theorem about Charon/Aeneas or Rust
compiler correctness. Input canonicality still must be supplied by the
accepted verifier's decoding path.

## Results and preserved failures

All 15 selected attempts exited 0. Their 51 axiom reports use only `propext`,
`Classical.choice` and `Quot.sound`. Maximum target RSS is 3,144,004 KiB,
total controller wall time for green attempts is 24.836 seconds, and every
green process swap count is zero. Jobs ran one at a time with MemoryHigh=4G,
MemoryMax=6G, MemorySwapMax=0, TasksMax=128, Lean `-j1 -M5000`, and a 300-second
timeout. No full regression or cold dependency build ran.

The archive preserves 60 attempt directories: 15 successes, 43 failed
compilations and two directories without receipts. Those two are explicitly
unclassified as compile results; neither is counted as successful. Failed
attempts and their axiom outputs are excluded from the successful theorem set.
The populated-polynomial proof hit the unchanged heartbeat limit while
elaborating a concrete field application. The replacement keeps the schedule
symbolic, fixes its universe and uses its finite equivalence directly. It
does not increase the heartbeat or memory cap or normalize a large recurrence.

## Import-source reconciliation

The original `populated-meaning-i` receipt has one mismatched source/object
association: its CallerModel source field records an uncompiled draft
`876ed33b...`, while the imported object is `5c9fdf5d...`. That object is exactly
the output of successful `caller-model-h`, whose source and immutable snapshot
are `4e675d196e...`. The manifest explicitly reconciles this one association
through the successful dependency receipt. Both original receipts and the
uncompiled draft are preserved; neither receipt is rewritten. The current
maintained CallerModel source is the successful h snapshot. This is not
evidence that the uncompiled draft passed.

`manifest.json` records every exact target, source/object hash, source revision,
wall time, RSS, swaps, direct-import pins, axiom reports and failed attempts.
Receipt source-base revision remains `b40d1cfffadbdf967f84cca23ea4e7f1553d564f`;
new sources are individually hash-pinned. `proofs.tar.gz` contains 561 indexed
files plus its summary. `source-review.md` audits the theorem premises,
source data flow and the recorded import discrepancy. The independent audit
checks the archive contents and reconciled object/source chain.

The historical semantic bridge, complete accepted-verifier implication,
extraction, privacy, Fiat–Shamir and runtime/settlement release obligations
remain open. This checkpoint makes no full 100-bit claim and no new CU claim.

| Target | Wall seconds | Peak RSS KiB | Axiom reports |
|---|---:|---:|---:|
| ExtractedMaskCoefficientArray | 1.217 | 2564776 | 3 |
| ExtractedMaskCoefficientSchedule | 4.356 | 3144004 | 10 |
| ExtractedMaskCoefficientStep | 1.662 | 2994676 | 6 |
| ExtractedMaskForwardRange | 1.475 | 2992276 | 4 |
| ExtractedMaskCoefficientLoop0 | 1.566 | 3005668 | 3 |
| ExtractedMaskCoefficientLoop1 | 1.547 | 3005448 | 3 |
| ExtractedMaskLinearsExact | 1.730 | 3001816 | 2 |
| ExtractedMaskConstants | 1.354 | 2994332 | 4 |
| ExtractedMaskCallerModel | 1.466 | 3003012 | 2 |
| ExtractedMaskCoefficientDecode | 1.281 | 2989060 | 1 |
| ExtractedMaskCoefficientScheduledSum | 1.471 | 2998800 | 1 |
| ExtractedMaskCoefficientWriteMeaning | 1.462 | 2994584 | 2 |
| ExtractedMaskCoefficientLoopMeaning | 1.681 | 3004540 | 4 |
| ExtractedMaskPopulatedMeaning | 1.812 | 3002248 | 5 |
| ExtractedMaskLinearMap | 0.756 | 1738872 | 1 |
