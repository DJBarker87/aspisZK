# R36: explicit source-shaped low residual polynomial

Parent `998ff7a2a200a054b65b1f9fbbc54345f90dba9b` (R35).
Branch `research/v8-r36-source-residual-model-20260929`.

**Result:** the low residual now has a concrete polynomial matrix, with
the T163 low table pinned and Lean-proved entry/matrix/determinant
evaluation identities. Its executable mirror matches all nontrivial
residual entries at both retained genuine prefixes, through independent
point/tensor/chord/weight comparisons. Sixteen new declarations compile.

This is **not** a nonvanishing theorem, a complete Rust-word/loop refinement,
a source sampling-law bound, or full privacy. No verifier or protocol path
changes, new hiding assumptions, or new CU savings are claimed.

## Explicit arithmetic rather than a free coefficient tensor

`ResidualModel.lean` defines the following operations over an arbitrary
commutative ring:

- `xEntry` and `xxEntry` from the retained integer carry schedules and
  powers of half. Their equality to R17's `sparseX`/`sparseXX` is proved.
- `chordEntry`, with the actual even/odd chord formulas. Its equality to
  `sourceChord` on every unit input j<1024 is proved, not supplied as a
  premise.
- The statement points: z, the suffix-product carry successor, and the
  coordinate-6/7 flip. The successor uses the full field expression
  `z_i + carry_i - 2*z_i*carry_i`, not a Boolean-only simplification.
- Big-endian multilinear tensor weights.
- T163's low inverse-dual weights, including the subtraction of the
  original pivot's tensor weight on inactive nonpivot rows.
- The point functional contracted against chord columns, using 111 code
  coordinates for the 108 potentially read quotient/weight coordinates.
- Four possible natural-basis shifts of the 23 query-factor coefficients,
  the three alpha-kernel channels, and the first 13 selected columns.
- The complete seven-coefficient four-slot convolution, with reversed
  weight slots `[0,3,2,1]` and the quarter factor.
- Both point observations, ordinary and structured relation polynomials,
  and the exact selected 13 residual rows.

The ordinary low weight is `kappa*E0+kappa^2*E1+kappa^3*E2`; the
structured low weight omits E0. The structured first point is zero on
these core-zero columns, while the ordinary first point is not discarded.
This uses the low-weight simplification checked in R34. Its universal
composition with the full source G/image/balance terms is still a source
refinement obligation; the model does not delete those terms in Rust.

Ring-homomorphism lemmas cover every arithmetic stage, including all
finite products, scatter sums, shift steps, and polynomial coefficients.
This lets polynomial evaluation commute with the explicit computation,
without expanding it into a huge normalized expression.

## Pinned T163 data

`ResidualPins.lean` is emitted by the checker only after comparing the
entire fixed source ORDER and INACTIVE arrays with the actual source
constructor (2,048 comparisons). It retains the first 111 order entries
and the inactive flag at each mapped original row. Its bound theorem
checks every retained original row is below pivot 1023.

Both prefixes emit byte-identical pins. The offline evidence gate also
independently parses those Lean lists back against the pinned full Rust
table. No permutation or inactive flag is supplied by a prover.

## The polynomial theorem that actually compiled

`ResidualPolynomial.polyMinor` is an explicit 13-by-13 matrix over
`MvPolynomial (Fin 38) F`. Variables are:

```
0..9    semantic challenges z
10      kappa
11      alpha
12..14  chord coefficients a,b,c
15..37  23 natural coefficients of the query-root polynomial P
```

Half and quarter are fixed coefficient-ring parameters. Evaluation at any
assignment equals the explicit pinned arithmetic matrix. Consequently,
evaluation of its determinant equals the determinant of that matrix.
These are universal **evaluation identities**. They do not assert that
the determinant is nonzero or that the assignment is source-admissible.

Unlike R34's degree-13 model with a free coefficient tensor, this object
specifies all point, transport, chord and convolution arithmetic. R34's
query-coefficient degree bound is not automatically promoted to a proved
degree bound for this new fully instantiated object; that composition
still needs its formal linearity/degree bridge.

## Executed source checks

The Rust mirror computes point coordinates from suffix products, tensors
from explicit bit tests, and chord entries from the small index model.
It then compares those values with the pinned source APIs. The original
accepted prefixes, challenges and queries are never substituted.

Per prefix:

| Check | Exact count |
| --- | ---: |
| Full T163 table/constructor comparisons | 2,048 |
| Natural multiplication unit entries | 756 |
| Chord unit entries | 11,988 |
| Chord-tail support assertions | 108 |
| Statement-point coordinates | 30 |
| Tensor coefficients | 3,072 |
| Low transported point weights | 324 |
| Full source low ordinary/G weights | 216 |
| Factor quotient coordinates | 1,404 |
| Nontrivial residual entries, all 13 columns | 208 |

All 271 G coins are also checked zero for each quotient column. Both full
seven-coefficient source polynomials are compared, not only boundary sums
or evaluation at alpha. The 208 count excludes the identically zero first
structured-point row and includes both remaining points and 14 polynomial
coefficients. Public 2704-byte model minors are retained.

Four negative-control families detect omitted pivot subtraction (all 324
point-weight entries differ), wrong big-endian ordering, replacing the
successor with independent bit flips, and failing to reverse the sumcheck
weight slots (all 13 ordinary-polynomial columns differ). Existing C1 and
other source regressions are unchanged, not unnecessarily rerun.

## Exact receipts

Source stage `/home/dombarker/project-offloads/aspis-r36-model-20260929-a`:
190 pins. Every inherited R34 source pin except the host target list is
unchanged; the new checker is the only added Rust target.

| Focused target | Exit | Wall | Peak RSS KiB | Swaps |
| --- | ---: | ---: | ---: | ---: |
| Release/offline/locked host compile | 0 | 20.61s | 517,768 | 0 |
| World0 source/model comparison | 0 | 0.02s | 2,464 | 0 |
| World1 source/model comparison | 0 | 0.02s | 2,464 | 0 |
| `ResidualModel.lean`, 12 declarations | 0 | 1.76s | 2,333,920 | 0 |
| `ResidualPins.lean`, one declaration | 0 | 1.42s | 2,328,552 | 0 |
| `ResidualPolynomial.lean`, three declarations | 0 | 1.08s | 2,262,688 | 0 |

All 16 final axioms audits contain only propext/Classical.choice/Quot.sound.
Initial local simp/composition/syntax failures are retained; statements
were not weakened, and limits were not raised. Nineteen predecessor
objects were reused by hash; after the model compiled its object was also
reused for the pins and polynomial bridge. No cold build or full replay.
Rust scope 5G/7G, Lean 3G/5G, MemorySwapMax0, TasksMax128; optimized Rust
with overflow checks enabled. Twenty-seven public evidence artifacts plus
their manifest are retained in `evidence/r36-source-residual-model`.

```
python3 docs/research/v8-full-view-zk-20260912/tools/check_r36_evidence.py
```

## First remaining proposition — do not skip source restrictions

Prove a nonzero determinant **after the source parameter restrictions**,
not merely for arbitrary 38-variable inputs. In particular:

1. a,b,c arise from the two circle points; use the R33 normalized chord and
   nonzero scale with justified denominator/admissibility conditions.
2. P is constructed from the 22 sampled fibre roots, not 23 independent
   uniform coefficients. Even its leading natural coefficient is fixed.
3. The matrix expression must be universally connected to the full source
   observations, including the low-support omissions and exact loop/field
   semantics. Two source comparisons are not that refinement theorem.
4. Only then derive an exceptional-event bound under the chronological
   shared-oracle/first-hit experiment. Algebraic variable assignments are
   not claims that those source challenges are independent or reorderable.

The observation rank, H1 coverage, adaptive posterior simulator, pre-beta
pair extraction, commitment/seed hops, visible failures/retries/publication,
and explicit losses remain open. The active goal is not complete. Selected
CU is unchanged at **1,620,236 / 1,621,719**; both actual 1M runs exhaust.
No SBF repeat, merge, deployment, or wallet operation occurred.
