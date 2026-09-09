# Adaptive final correction: a proved far-final regression

`AdaptiveFinalPrior.lean` proves that a post-alpha final can repair the
**actual carried relation prior**. This rules out a shortcut in the unfinished
far-final argument; it is not an accepting-proof construction or a payment
forgery. The exact change to queried values is proved alongside the correction.

## Statement and causal scope

For the existing `PostQueryFunctional.Prefix`, write `w=p.foldWeight` and
`c=p.carried`. Both include the actual compact response0, alpha0 and carried
image functional; no image or row check is removed. For any baseline final
`F0 : Fin 256 -> K` and any coordinate `j` with `w[j] != 0`, define

```
delta = (c - dot(w,F0)) / w[j]
F = F0 + delta * e_j.
```

The theorem constructs this `F` and derives:

- `p.prior F = 0`;
- only coefficient `j` changes, by exactly `delta`;
- its natural polynomial has degree at most255, so the final256 field grammar
  is unchanged;
- if `p.prior F0 != 0`, the changed final is not `F0`;
- every actual query residual changes by
  `delta * naturalLineValue(queryPoint,j)`.

The construction uses the prefix after alpha0 and does not use future
queries, rho or later relation challenges. `p.prior` and `p.foldWeight` do not
read the analysis reference quotient. No received-word polynomiality,
candidate membership, valid witness, honest trace, or nonzero incoming prior
is assumed in the existence theorem. The coordinate-nonzero condition is
explicit; this report does not assert it at every possible prefix.

`corrected_query_residual` is important: changing one **coefficient** does not
mean changing only one **evaluation**. The new term can alter every query
value. The theorem does not assert how many fibres now match the fixed
received word, nor that any fixed precommitment can realize favourable
matching sets across challenges.

## Consequence for the joint recovery task

V7's existing degree bounds remain valid in their correct scope. A first-round
degree-six error bounds repair against a fixed reference fold. The actual
prior with a different adaptive final has the additional term

```
prior(F) = firstError(alpha0) - dot(foldWeight, F - referenceFinal).
```

The new theorem demonstrates that this extra term cannot simply be omitted.
Likewise the full degree-28 component-claim error is not, by itself, a
nonzero-prior guarantee after adaptive final selection. No fixed-target or
same-final theorem is contradicted.

The fixed-C1 reduction must retain both kinds of structure:

| Object | Existing proved scope | Far-final obligation |
|---|---|---|
| Early recovered C1 and its own support | `FixedC1HelperReduction.raw_batch_on_c1_support` and `restricted_support_iff` | Do not replace received C1 outside that support |
| Raw three-helper curve | Degree at most2, fixed after C2 and before gamma | This is not the degree of the normalized false-OOD quotient |
| Ordinary and OOD claim errors | Full degree at most28; the low C1 error survives normalization | Keep the reciprocal-power OOD term from `QuotientHelperShift` |
| Actual post-alpha final | May be selected in the affine constraint `dot(w,F)=c` | Bound its matching mass jointly with the fixed received helper curve |

The next quantitative target is the query-passing mass for actual
relation-compatible adaptive finals, with the shifted query batch and later
repair events retained. A final chosen only to zero the prior is not already
an attack; a bound on claim roots alone is not already a defense. No new
probability estimate or global security subtotal is supplied by this leaf.

## Proof/source status

| Declaration | What is kernel checked |
|---|---|
| `dot_single_update` | Exact dot-product update for arbitrary dimension and field values |
| `corrected_at`, `corrected_away` | Literal single-coordinate field-vector update |
| `corrected_prior_zero`, `exists_adaptive_prior_zero` | Repair of the existing modeled carried prior |
| `corrected_degree` | Reuses the V7 natural coefficient polynomial degree bound |
| `corrected_ne` | A wrong old prior requires a genuinely changed final |
| `corrected_query_residual` | Actual source-shaped natural evaluation residual change |

The imported `PostQueryFunctional` derives weights, compact claimed scalars,
natural evaluation and shifted batch from the existing modeled grammar.
This is a kernel-checked field-level result, not a fresh Rust/Aeneas
translation, parser/authentication theorem, SHA/replay coupling or test of a
complete pool transaction. The corrected vector has the same256 field
positions; no protocol check, message or production source was changed.

## Reproduction and evidence

```
bash docs/research/v8-no-work-100-20260907/experiments/run_adaptive_final_prior.sh \
  docs/research/v8-no-work-100-20260907/experiments/adaptive-final-prior-v2.log
```

The guarded runner refuses an existing output log, compiles only this leaf,
uses Lean `-M7000`, and stops the child tree at7,340,032KiB aggregate RSS. It
checks the committed research source closure, borrowed V7 source pin, Mathlib
revision and input olean hashes; pre/post provenance was unchanged.

| Run | Exit | Wall | Peak RSS | Swaps | Scope |
|---|---:|---:|---:|---:|---|
| [v1](experiments/adaptive-final-prior-v1.log) | 1 | 69.01 s | 3,739,025,408 B | 0 | Only final residual-name ambiguity failed |
| [v2](experiments/adaptive-final-prior-v2.log) | 0 | 34.08 s | 5,055,791,104 B | 0 | All8 printed declarations standard-only |

The sole v2 change qualifies `PostQueryFunctional.residual`; no theorem
premise or field expression changed. Final axioms are only `propext`,
`Classical.choice`, `Quot.sound`; no `sorry` or new axioms in the green leaf.

- Research pin: `edb199c12fcc41f00330298b95b4736f60ac6f3a`.
- Borrowed formal source pin: `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.
- Lean4.32.0 commit: `8c9756b28d64dab099da31a4c09229a9e6a2ef35`.
- Mathlib: `81a5d257c8e410db227a6665ed08f64fea08e997`.
- Source SHA256: `037aa924363aa6e0ff070d4cca2fdddee26af01d2c6cef28d0cd4d27c96f7d9e`.
- Olean SHA256: `1ec461fadb753f8ef55d1a9136cdea1f8c7df32ecb2c0780b4e44f8d1b3e6b0d`.

The unrelated natural-binary bridge is frozen as a
[failed diagnostic](natural-binary-polynomial-diagnostic.md), not imported or
claimed proved here. There is no new wire, CU, prover-time, extraction-time,
privacy or Fiat–Shamir result, and no grinding credit.
