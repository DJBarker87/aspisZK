# R12 three-cut evidence

Source base: `9f0dab29ca0920e82ef7cfca0e9831d44e1ca9d2`.
Scope: exact three-cut G arithmetic and algebraic transports only. This is not
a seeded-SHA, C2-prefix, complete-transcript, or publication theorem.

## Locked checks

- Pack manifest: 50/50 passed.
- Source pins: 11/11 matched; dependency closure is not asserted.
- Python: 48/48 passed, including retained R11 inverse checks, two R12
  certificates, 941-coordinate complement and raw-tape bijections.
- Independent C++: 378 polynomial instances, two determinant certificates,
  and seven joint-82 rank instances passed.

## Lean

The supplied `PairCancellation` draft required an explicit
`Mathlib.Algebra.Field.Basic` import in this cached Mathlib; `KernelSection`
needed the same narrow API repair. No theorem statement was weakened.

All six leaves and `AspisV8R12.lean` compiled with `lake env lean -j1 -M1800`.
Peak RSS by leaf was 1.74, 1.36, 1.37, 1.32, 1.33 and 1.30 GB; aggregate peak
RSS was 1.71 GB. Every run reported zero swaps. Printed axioms are limited to
`propext`, `Classical.choice`, and `Quot.sound` as applicable.

The compiled results establish the boundary-operator identities, symmetric
prefix partition, pair cancellation, conditional kernel section, causal
three-cut equivalence/posterior fibre, and raw-skeleton transport assuming an
exact codec. They do not instantiate a real SHA codec or commitment hybrid.

## Rust source checks

Compiler: `rustc 1.93.0`. Feature: `insecure-spend-fixture`; release/offline.

- `r12_balanced_g_cut`: pass (2 tests), 2.94 s wall, 146,161,664 bytes maximum RSS,
  zero swaps. It checks actual G-factor rows, inactivity, exact prior-round
  cancellation, boundary zero and full 27-coordinate rank for Boolean and
  non-base QM31 prefixes. Its fixed boundary/moment inverses plus polynomial
  translation lift every coordinate and an arbitrary 27-vector, checking the
  entire compact image and all prior polynomials.
- appended `r12_complete_selected_terminal_preserves_earlier_rounds`: pass,
  3.42 s wall, 161,660,928 bytes maximum RSS, zero swaps. It uses the genuine
  compiler fixture and complete selected terminal through rounds 0..2.

The existing C1 q4/q6 negative regression, R10 H1 boundary, and fail-closed
publication path remain unchanged.

## First remaining proposition

Construct the source-instantiated reversible payload map across the actual
main-seed rejected-word expansion and paired C2 commitments in the one shared
oracle: preserve prior answers, salts, C1/H1 and non-G accepted words; replace
both old/new typed C2 leaf preimages consistently; and prove no additional
selected-G read occurs before the first three semantic messages. Hidden-input
hits, rejection/abort mass, retries and publication stopping must remain
explicit. The exact arithmetic and ideal raw-skeleton equivalence here do not
prove that proposition.
