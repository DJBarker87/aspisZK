# Scope of the port: the two agreement theorems over the wide field

2026-10-05. Research note. This is gap 1 of `R0_SOUNDNESS.md`. No file under
`AspisFormal/` is changed.

## Target

Two theorems, today proved over the 124-bit field `QM31Exact`, restated over
the 248-bit field `WideExact`:

```lean
exactV7InitialWidth29CurveDecodable :
  Width29CurveDecodable exactInitialEncoder 38229 initialBatchChallengeCap
exactV7FinalDegreeThreeCurveDecodable :
  DegreeThreeCurveDecodable exactFinalEncoder 9557 foldChallengeCap
```

Same encoders, same thresholds, same caps. Only the field of the lanes, the
challenges and the codewords changes.

## What exists after this note

`lean/WideTower.lean` builds the wide field in Lean and compiles with a clean
axiom audit:

- `WideExact := QuadraticAlgebra QM31Exact wideU 0`, one more quadratic layer
  on the deployed tower (`v^2 = u`, `u^2 = 2 + i`);
- `qm31_wideU_not_isSquare`: `u` is a non-square in QM31, by a norm argument
  from the existing `cm31_qm31R_not_isSquare`. Mathlib then supplies the
  `Field` instance;
- `wideExact_card : Fintype.card WideExact = P ^ 8`;
- `wideExact_natCast_ne_zero_of_pos_of_lt_characteristic` and
  `wideExact_two_ne_zero`;
- `qm31_to_wide_injective`: QM31 embeds.

| Target | SHA-256 | exit | wall | peak RSS | swaps | axioms |
|---|---|---:|---:|---:|---:|---|
| `lean/WideTower.lean` | `f55bd736f0e8…c34c538` | 0 | 147 s | 2,999 MB | 0 | 5 reports, `propext`, `Classical.choice`, `Quot.sound` only |

Compiled locally with `lake env lean -j1 -M4500` in the existing
`/Users/dominic/ZK/AspisFormal` workspace against its cached objects of 13
September; source revision `acd4c0f0d`. One first attempt failed on a single
`simp` goal and was fixed in the proof, not by changing a statement.

## Size of the dependency

Import closure of the two theorems inside `AspisFormal/`:

| | files | lines |
|---|---:|---:|
| Closure | 267 | 132,311 |
| Never mention `QM31Exact` or `CM31Exact` | 228 | 116,412 |
| Mention them | 39 | 15,899 |

The 39 files split three ways.

| Group | files | lines | Concrete field computation |
|---|---:|---:|---|
| Mathematics: 22 agreement files, the list-bound file, 3 encoder files | 26 | 11,892 | none |
| V7 transcript context: sampler values, limb and byte encodings, secure-circle map, K1.2–K1.4 classifiers, C1 projection | 12 | 3,636 | in 4 of them |
| The tower file itself | 1 | 371 | yes |

In the 26 mathematical files the field appears only as a type. A scan for
`decide`, `norm_num`, limb, byte, Karatsuba, inverse-table and coordinate
(`.re`, `.im`) usage on lines naming the field finds nothing there.

Field facts the mathematical files use by name:

1. the field is finite and its size is known (`qm31Exact_card`, used once, in
   `V7ExactCorrelatedAgreementSmooth.lean`);
2. naturals below `p` are nonzero
   (`qm31Exact_natCast_ne_zero_of_pos_of_lt_characteristic`);
3. `2 ≠ 0`;
4. an algebra map from `ZMod p`. The encoders and the GRS evaluation points
   are defined through it: the GRS point is `y / (1 + x)` computed in
   `ZMod p`. Nothing needs `i` in the challenge field.

`WideTower.lean` provides 1–3; 4 is an instance.

## Probe: substitute the field and recompile

Three central files were copied to scratch, `QM31Exact` was replaced by
`WideExact` textually, and each was compiled against the unmodified cache.
Nothing else was edited.

| File | lines | mentions | Result |
|---|---:|---:|---|
| `V7ExactCorrelatedAgreementFactors` (holds the characteristic-dependent separability step) | 650 | 8 | **compiles, 0 errors**; 84 s, 3.5 GB |
| `V7ExactCorrelatedAgreementFunctionField` | 297 | 17 | 1 error: it calls the characteristic lemma of the *original* `Factors` file, which is QM31-typed |
| `V7Tag73ExactOneFoldEncoderBinding` (defines the final encoder) | 262 | 37 | 3 errors: two references to the QM31-typed `exactInitialEncoder` of another file, one elaboration timeout downstream of them |

All four errors are at seams with neighbours that were not substituted. None
is a failure of a mathematical step under the new field. Zero swaps in all
runs.

This is evidence that the port is mechanical. It is three files of 26, and
the list-bound file, the GRS conversion and the long Hensel files were not
tried.

## Method

Copy, do not edit. V7's formal release has frozen manifests and a recorded
336-target replay; changing its files would invalidate them. The port should
be a parallel set of files, generic in the field, that V7 never imports.

1. Field-generic encoders. Extract `exactInitialEncoder`, `exactFinalEncoder`
   and the GRS conversion (3 files, 818 lines) into versions parametrised by
   a field `K` with `[Algebra (ZMod p) K]`, cutting their imports of the V7
   context files. This is the only step that needs design rather than
   substitution: the encoder definitions sit inside files that also carry V7
   projection lemmas.
2. List bound (`V7Tag73ExactMultiplicityThreeGS`, 1,285 lines).
3. The 22 agreement files (9,789 lines), in dependency order, compiling each
   before the next.
4. Instantiate at `WideExact`. Instantiate also at `QM31Exact` and check the
   two statements obtained are the V7 statements verbatim; that is the
   regression test.
5. Three small lemmas the paper proof needs that are not in the tree: the
   matched form for degree three (its gap 2), the joint-list bound (gap 5)
   and subfield descent.

Every compile so far fits the local 8 GiB rule (at most 3.6 GB). The full
pass is 26 files; the three probes took 84 to 173 s each, mostly import
loading.

## Risks

1. **Elaboration cost.** `WideExact` is three nested quadratic algebras.
   Instance search and unification are slower; one probe hit a heartbeat
   limit, though behind a type error. Long files may need local limits.
2. **Instance paths.** One probe error shows the two fields reaching `Nat.cast`
   through different instance chains. A generic-`K` formulation avoids this;
   a textual copy would meet it wherever `simp` normal forms differ.
3. **Untested files.** The list bound, the GRS conversion and
   `HenselIntegralLift` (1,687 lines) are the largest unknowns.
4. **Step 1 is not substitution.** If the encoder definitions cannot be
   separated cleanly from the V7 context, 12 more files (3,636 lines), four
   of them with concrete QM31 arithmetic, come into scope.
5. This port delivers gap 1 only. The Fiat–Shamir theorem and the semantic
   bound remain the larger items.
