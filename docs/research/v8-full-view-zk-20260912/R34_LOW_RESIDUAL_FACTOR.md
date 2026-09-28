# R34: factor the low G residual without changing the verifier

Parent `03549062720acd4fe4ca87f1eac82391e069f2ca` (R33).
Branch `research/v8-r34-low-residual-factor-20260928`; checks ran 2026-09-29.

Result: both retained genuine prefixes pass the query-factor basis change
and the complete low-block source weight simplification. Eight new Lean
declarations compile. **Universal source residual coverage, full privacy,
and the 1M-CU target are still open.** No verifier/protocol/transcript change,
new hiding assumption, reference removal, or new CU saving is claimed.

## Source-checked factor basis

Let P(t) be the monic polynomial with the 22 actual query-fibre roots.
R33 uses the natural-basis remainders E_d - rem(E_d,P): all three channels
for d=22..25, then channel B at d=26. R34 replaces these with the same
channels of P(t)t^j, j=0..3, followed by channel B of P(t)t^4.

The checker constructs P and its multiples using the pinned source
`times_x`; it does not substitute query roots or earlier challenges.
The high natural coefficients form an upper-triangular 13-by-13 matrix U.
It checks all 13,312 quotient-vector coordinates in `Q_factor=Q_normal*U`
and all 221 residual entries in the corresponding observation identity.
The reconstructed normal minor agrees with all 169 committed R33 entries.

For these source constructions the diagonal coefficient at degree d is
`half^(d-popcount(d))`, where half=1/2. The degrees give exponents
19,19,22,22 (each three times), then 23. Thus the determinant scale is
`half^269`. Both actual source minors satisfy

```
det(factor minor) = det(normal minor) * half^269 != 0.
```

This removes the normalized remainder divisions from the candidate
polynomial expression. It does **not** eliminate P or its query-root
dependence. The source recurrence/leading-coefficient formula and the
triangular change have been checked here, not yet universally Lean-refined.
The Lean basis-change theorem explicitly retains `det(U)=half^269` as a
premise; it must not be reported as having proved that source premise.

## Complete polynomial locality, not just a scalar equality

The low quotients are supported below index 106. The first relation
polynomial convolves each four-slot quotient chunk with the reversed
dual weight chunk, so weights through index 107 can affect it.
Checking only the scalar pairing or weights below 106 would be insufficient.

Write E_i for the actual point-i tensor functional transported through
T163 and the source chord adjoint. On **all first 108 weight coordinates**,
both prefixes satisfy

```
w_R = kappa*E_0 + kappa^2*E_1 + kappa^3*E_2
w_G =             kappa^2*E_1 + kappa^3*E_2.
```

These are 216 source equalities per prefix, using the full source weights
including their structured-G, inactive/balance, and image additions.
Those additions vanish on the relevant chunks; they are not removed from
the verifier. The distinction between the ordinary first point and the
structured first point remains. The latter is zero on these G-core-zero
columns; the two retained ordinary point observations are still present.

`low_coefficient` proves locality for the retained source-shaped four-slot
coefficient kernel, at every coefficient index. `point_reduction` applies
the point-weight identity to every such coefficient. The support and weight
identities remain explicit premises. R33 supplies a source-shaped chord
support theorem; a complete Rust/T163/field refinement is not newly claimed.

## Query-coefficient degree, with the right scope

With all non-query parameters fixed, the factor-basis residual matrix is
linear in the 23 natural coefficients of P. The checker evaluates all 23
coefficient basis directions, all 13 columns, and reconstructs every one
of the 221 actual residual entries. These **299 algebra probes per prefix**
are not new source-generated transcripts and do not resample masks.

The Lean model defines each 13-by-13 entry as `sum_d a[i,j,d]*X_d`, proves
its evaluation formula and total degree at most one, and proves determinant
degree at most 13. It also proves determinant evaluation and the nonzero
basis-change equivalence. The coefficient tensor's universal source
correspondence, symbolic nonzero witness, and root substitution still need
their own proof; a degree bound is not a probability bound.

In particular, later query sampling must not be silently reordered before
earlier semantic/Fiat--Shamir challenges. No independence, source-exception
probability, or negligible global failure probability is assigned here.

## Exact receipts

Stage `/home/dombarker/project-offloads/aspis-r34-factor-20260929-a` has
189 pins. Every inherited R33 pin except the host Cargo target list is
unchanged. Only one host checker/target was added. Both original 424-byte
prefixes and the R33 public minor hashes are checked by the evidence gate.

| Target | Exit | Wall | Peak RSS KiB | Swaps |
| --- | ---: | ---: | ---: | ---: |
| Release/offline/locked host compile | 0 | 18.46s | 516,660 | 0 |
| World0 source/factor checks | 0 | 0.05s | 2,640 | 0 |
| World1 source/factor checks | 0 | 0.06s | 2,640 | 0 |
| Retained `BetaUniformCorrection.lean` prerequisite | 0 | 0.89s | 1,704,828 | 0 |
| New `LowResidualFactor.lean`, eight declarations | 0 | 1.05s | 2,126,788 | 0 |

The first Lean attempt omitted the nontrivial-ring condition needed for
the library's degree-of-X lemma; its failed receipt is retained. The fix
adds that condition only to the two degree lemmas. The final eight axioms
audits contain only propext/Classical.choice/Quot.sound, with no sorryAx.
Sixteen R33 objects and then the prerequisite object were reused by hash.
There was no full manifest replay or cold dependency build.

Rust scope: MemoryHigh5G/MemoryMax7G/MemorySwapMax0/TasksMax128;
Lean: 3G/5G/0/128. Rust release overflow checks stay enabled. The Solana
testing skill kept these host/algebra checks distinct from CU measurements.
Wrong determinant normalization and omitting the first-point distinction
are detected by two negative controls per prefix. Existing C1 and other
negative regressions are untouched, not needlessly rerun.

Twenty public artifacts plus their manifest are in
`evidence/r34-low-residual-factor`. Gate:

```
python3 docs/research/v8-full-view-zk-20260912/tools/check_r34_evidence.py
```

## First remaining proposition

Bind the factor-basis 13-by-13 matrix **universally** to the actual source
recurrences, T163 dual and three statement points; prove the associated
nonzero determinant polynomial and justify its exceptional set under the
actual chronological shared-oracle/query law. R34 simplifies this task but
does not discharge it. R33's residual right-hand-side adjustment remains
`b-B*A^-1*a`; the low-column simplification does not permit dropping it.

Current-layout H1 coverage, posterior-preserving adaptive simulation,
pre-beta quotient-pair extraction, commitment/seed hops, visible failures,
retries/publication, and explicit security losses remain separate gates.
Selected verifier CU remains **1,620,236 / 1,621,719**; both actual 1M runs
exhaust. No unchanged SBF run, merge, deployment, or wallet operation occurred.
