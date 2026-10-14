# Fractional-lift inverse and exceptional gamma evidence

Source base: `496110fcb2202fc8094191241f067a972071d396`.

This bundle records focused NUC compilation of the five components and their
combined checkpoint. Each target ran in a separate capped scope with
`MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`, and `TasksMax=128`.
Every final target exited zero, with zero swap and only `propext`,
`Classical.choice`, and `Quot.sound` in its axiom reports.

| Final target | Attempt suffix | Wall time | Peak RSS (KiB) | Axiom reports |
| --- | --- | ---: | ---: | ---: |
| R1FractionalLiftInvolution | fractional-lift-involution-f | 1.55 s | 2,682,864 | 4 |
| R1NaturalPairInverse | natural-pair-inverse-c | 1.31 s | 2,876,520 | 4 |
| R1CircleNumeratorInverse | circle-numerator-inverse-j | 1.39 s | 2,879,476 | 6 |
| R1GRSMessageInverse | a | 1.22 s | 2,871,488 | 2 |
| R1GammaSubfieldBound | gamma-subfield-bound-z | 1.13 s | 2,468,332 | 5 |
| R1LiftSubfieldCheckpoint | lift-subfield-checkpoint-a | 1.16 s | 2,866,220 | 21 |

All 47 attempts are retained: 39 failed, two superseded green, and six final.
The final targets produce 42 reports, including the checkpoint's repeat audit
of 21 declarations. Including the superseded green attempts gives 45 successful
reports; these counts are not counts of distinct proved theorems.

The source manifest pins snapshots, receipts, resource logs, final sources,
runner/environment files, and the six compiled objects. Objects are retained
only in `objects/lift-subfield-objects.tar.gz`, SHA-256
`f7de1f133760461921d8f24e04f13ad305eafe369631233baaf5bd0be1990dbf`.
`ROOT-VALIDATION.json` records the independent root audit; `SHA256SUMS` seals
all bundle files except itself.

The mathematical scope is described in
[GRS-MESSAGE-INVERSE.md](../../GRS-MESSAGE-INVERSE.md) and
[GAMMA-SUBFIELD-BOUND.md](../../GAMMA-SUBFIELD-BOUND.md).
The inverse remains a noncomputable finite algebraic specification. The gamma
bound is for the existing independent uniform-block modulo model. This bundle
does not close executable decoding, Rust correspondence, adaptive Fiat–Shamir,
or universal privacy obligations.
