# Four exact folds construct a bounded polynomial quotient

The two new leaves are kernel-checked:

- `ChordRationalDivisibility`: four distinct exact cleared-fold equations force componentwise norm divisibility and construct an exact polynomial quotient when the norm is nonzero.
- `ChordRationalQuotientDegree`: if all four supplied finals have degree at most255, the **same constructed quotient** has four components of degree at most255 and folds to each supplied final.

This closes the algebraic existence/degree step. It does not assert that an arbitrary committed oracle has polynomial components, or that this representation has already been connected to the source encoder/image and the complete causal acceptance experiment.

## Precise statement

Let `K` be a field, `s=X`, `t=1-X`, and use the existing low-bit `[1,y,x,xy]` product. For fixed chord coefficients `a,b,c` and polynomial vector `u`, put

```
L   = line(C a,C b,C c)
Adj = clearedAdjugate(a,b,c)
N   = clearedNorm(a,b,c)
W   = product(s,t,u,Adj).
```

Assume four distinct challenges `alpha_i`, four polynomials `F_i`, and the **full polynomial identities**

```
W0 + C(alpha_i)*W1 + C(alpha_i)^2*W2 + C(alpha_i)^3*W3 = N*F_i.
```

The finals may differ at every challenge. These hypotheses are stronger than a single queried evaluation agreeing: the new theorem does not infer a polynomial identity from such an agreement.

Then every `Wj` is divisible by `N`. If `N≠0`, the theorem constructs `q` such that

```
u = product(s,t,q,L).
```

If additionally `natDegree(F_i)≤d` for all four actual supplied finals, it constructs that same `q` with `natDegree(q_j)≤d` for every component, and

```
foldedNumerator(alpha_i,q) = F_i
```

for all four challenges. The final256 corollary sets `d=255`. Neither the raw component degree nor a presumed degree-two norm is required by this implication. A nonzero norm of smaller degree is handled identically. `N≠0` means a nonzero **polynomial**; it does not claim the denominator is nonzero at every domain position. Pole/query accounting remains separate.

## Why this is a construction

The principal ideal of multiples of `N` is restricted to a `K`-submodule of `K[X]`. Each exact cleared equation places one cubic evaluation in that submodule. The [four-point lemma](four-point-submodule-review.md), reusing the existing `ExactFoldRecovery` Lagrange proof, therefore puts every `Wj` in it. The polynomial divisibility witnesses provide `q_j` with `Wj=N*q_j`.

New symbolic four-component ring lemmas prove associativity, commutativity and scalar factoring for the actual `product` definition. Together with the existing `line_adjugate` identity they give

```
product(W,L) = N*u = N*product(q,L).
```

Cancellation in `K[X]` gives the reconstruction. No candidate membership, expected quotient, successful decoder, assumed product associativity or successful witness validator is supplied.

For the degree step, reconstructing `u` yields `W=N*q`. Factoring `N` through each actual folded numerator and cancelling it identifies the fold of `q` with that challenge's supplied `F_i`. A second application of the same four-point theorem, now to Mathlib's existing `Polynomial.degreeLE K d` submodule, bounds every `q_j`. The zero polynomial is handled correctly by the degree-submodule API. No subtraction of an assumed norm degree or generic-leading-coefficient assumption is needed.

## Remaining interpretation obligations

The returned objects are four ordinary radial polynomials of bounded degree with the exact product identity. They are not yet a literal source message vector plus a proved encoder/image correspondence. Translating the radial/final variable convention, reattaching any affine interpolant to the raw word, deriving image/original-code membership, and coupling the exact-versus-nonzero-discrepancy split to actual accepted executions remain consuming obligations.

The result supports adaptively selected finals as distinct polynomial inputs. It does not establish a fresh conditional Fiat–Shamir challenge law, four legal replay branches, an efficient witness extractor or the probability of reaching these four identities. In particular, source polynomiality and the same fixed `u,L,N` across the four challenges are substantive prerequisites; no arbitrary received oracle is silently converted into a polynomial.

The proof is research-only and changes no transcript, verifier check, proof-body byte, field/domain/query profile or production setting. The accepted allowance remains40,282 bytes. No CU, prover, SBF, rank or privacy measurement is reported here.

## Focused evidence and provenance

Research HEAD: `edb199c12fcc41f00330298b95b4736f60ac6f3a`. Borrowed formal source closure: `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`. The runners verify the exact green source/olean hashes of Algebra, Degree, FourPointSubmodule and ExactFoldRecovery before/after each new leaf; unrelated concurrent main commits are not imported. No unchanged dependency was rebuilt.

| Leaf/check | Exit | Wall | Peak RSS | Swap |
|---|---:|---:|---:|---:|
| [Divisibility v1](experiments/chord-rational-divisibility-v1.log) | 1 | 38.00 s | 5,441,388,544 B | 0 |
| [Divisibility v2](experiments/chord-rational-divisibility-v2.log) | 0 | 14.19 s | 5,646,319,616 B | 0 |
| [QuotientDegree v1](experiments/chord-rational-quotient-degree-v1.log) | 0 | 25.06 s | 5,571,543,040 B | 0 |

The failed divisibility attempt left finite-vector literal projections unreduced by an incomplete `simp only` list. The ring tactic then treated vector applications as atoms; its associativity declaration exhausted200,000 heartbeats. The already independent principal-ideal/divisibility theorem passed. Replacing the incomplete four-coordinate reducer with the existing Algebra leaf's `simp [product]` pattern closed the ring identities **without raising any limit** or altering the divisibility statement. This is a fixed four-coordinate symbolic operation, not normalization of a generated concrete-field expression. Temporary failed-diagnostic `sorryAx` is absent from both final audits.

All ten Divisibility and six QuotientDegree audits use only `propext`, `Classical.choice`, `Quot.sound`. Retained source contains no added axiom or `sorry`.

| Artifact | SHA-256 |
|---|---|
| Divisibility source | `a44903575cbc9d2cb91c78433aec01ce10bcc39518c61c79d977e077f84b8b67` |
| Divisibility olean | `08a1779198e669674c19e83c5fdf286d78373ee1f3c982f5ecd36095d0582352` |
| QuotientDegree source | `faec5edccc72c31ca400a24f9a77202494efe5bc465a6a742ac2e0d82d71fa26` |
| QuotientDegree olean | `6036545aa197cbebebfc6e72fc9f87d6d41f7a4579aee0733e0122358e528574` |

Lean4.32.0 is pinned at `8c9756b28d64dab099da31a4c09229a9e6a2ef35`; Mathlib at `81a5d257c8e410db227a6665ed08f64fea08e997`. Every job used an explicit serialized parent build-slot grant, Lean `-M7000` and the7,340,032-KiB aggregate child-process RSS guard. No Rust or SBF job was run.

Archived exact commands:

```sh
bash docs/research/v8-no-work-100-20260907/experiments/run_chord_rational_divisibility.sh \
  docs/research/v8-no-work-100-20260907/experiments/chord-rational-divisibility-v2.log
bash docs/research/v8-no-work-100-20260907/experiments/run_chord_rational_quotient_degree.sh \
  docs/research/v8-no-work-100-20260907/experiments/chord-rational-quotient-degree-v1.log
```

These filenames are archived evidence. Each runner requires a fresh filename for any justified changed-source rerun.
