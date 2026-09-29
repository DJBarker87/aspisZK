# R40: certify the restricted residual specialization and its nonvanishing

Parent `84059b5296757f31bfc40f0be52e31de76aa2894` (R39).
Branch `research/v8-r40-residual-entry-certificate-20260929`.

**Result:** 481 new Lean theorems compile with standard axioms only. All
169 model-entry equalities and 169 inverse-product entries are checked;
the final restricted-polynomial nonzero theorem and offline evidence gate
pass. The coefficient ring for this result is `ZMod 2147483647`.

This stage completes the concrete M31 algebraic-witness certificate begun
in R37–R39. It connects the actual explicit polynomial model to the literal
13-by-13 matrix, proves that matrix has a right inverse, and uses polynomial
evaluation to prove the restricted determinant polynomial is not zero.
It is **not a full privacy proof or a probability bound for the source**.

## The exact specialization

The witness is unchanged: z = [2,...,11], kappa = 5, alpha = 7,
u = 2, v = 3, roots = [1,...,22]. The normalized chord is (7,5,-5),
half = 1073741824 and quarter = 536870912 in `ZMod 2147483647`.
These roots and OOD parameters are algebraic test values, **not an accepted
source transcript or a replacement for either genuine retained prefix**.

R38 already certifies the root polynomial and its four shifts. R39 already
certifies the three point/code/chord-weight arrays. R40 establishes:

1. The model's 23-to-27 zero padding equals the certified p22 vector.
2. Each of the 13 model quotient columns equals its literal 108-vector.
3. The ordinary weights are `5*E0+25*E1+125*E2`, and the G weights are
   `25*E1+125*E2`; all 216 low entries are checked separately.
4. All 169 selected residual entries equal the retained R37 matrix.
5. The displayed literal right inverse multiplies that matrix to identity.
6. The exact `assignedMinor` is this matrix, so its determinant is nonzero.
7. `SourceResidualPolynomial.determinant_evaluation` then proves
   `(SourceResidualPolynomial.polyMinor half quarter).det ≠ 0` over M31.

The last theorem is `WitnessEntryData.restricted_polynomial_ne_zero`.
Its statement has no unproved concrete-matrix premise. The root construction,
normalized-circle substitution, fixed T163 table, point carries, balancing
correction, quotient columns and observation layout remain in its dependency
chain. This is not a standalone proof about an unrelated numeric matrix.

The selected rows remain [1,2,3,4,5,6,7,8,10,11,12,13,15]. The two point
rows, six ordinary coefficients and five G coefficients are not collapsed
into one functional. The polynomial convention remains the four-slot
reverse [0,3,2,1] and factor one quarter.

## Why the kernel check stays small

`ResidualEntryCertificate.sum108` is a generic identity splitting a
108-term sum into four contiguous 27-term sums. `poly_slots` is a generic
identity expanding only the two four-slot indices of `polyCoeff`, retaining
the 27-block outer sum. The generator emits applications of these named
lemmas. It does not unfold the root recurrence or recompute the point weights
inside every residual entry.

Each column has eight partial dot sums, two completed dot sums, eleven
polynomial coefficients and thirteen observation bridges. Quotient columns
rewrite R38's named shift theorems before checking their coordinates.
The matrix bridge combines the 169 observation theorems.

An optimized host Gaussian elimination supplies an inverse candidate. Lean
checks every one of its 169 product entries using ordinary kernel `decide`,
in thirteen row-sized files. A generic commutative-ring lemma turns the
checked right inverse into determinant nonvanishing. The only needed
nontriviality fact, `0 ≠ 1` in this concrete ring, is itself checked by the
kernel. No primality assumption, assumed determinant value or trusted native
determinant evaluator is needed for this result.

The earlier executed determinant value 1171866436 remains retained evidence.
R40 proves nonvanishing through an inverse; it does not claim a new formal
proof of that particular determinant residue.

## Source checks and their boundary

The optimized generator verifies the same pinned T163 inventory and uses
the actual source statement points, weight accumulator, dual transport and
chord transpose. It compares:

- 216 low ordinary/G weight entries with source `quotient_weights`;
- 1,404 quotient coordinates with the independently built source columns,
  including the zero extension beyond the low window;
- 208 source observations, using original-space point pairing and
  `polynomial_for_extension` for both channels;
- all 169 exported minor entries byte-for-byte with R37's retained matrix;
- 169 inverse-product entries before generating the Lean certificates.

The source structured-G coins remain zero on these candidate correction
columns. The wrong polynomial-slot convention differs in all thirteen
columns and remains a negative control. Existing C1 negatives are untouched.

These are finite executable source comparisons for an algebraic witness.
They do **not** establish universal Rust semantics, an accepted-prefix
distribution, or adaptive coverage. The formal result is about the explicit
R36/R37 model. R37's two genuine source-prefix comparisons remain distinct
retained evidence; they were not replaced or rerun unchanged here.

## Focused verification and retained failures

| Final focused target | Exit | Wall | Peak RSS KiB | Swaps |
| --- | ---: | ---: | ---: | ---: |
| Optimized Rust generator compile | 0 | 19.75s | 517,100 | 0 |
| Generic contraction lemmas | 0 | 1.80s | 2,287,948 | 0 |
| First full residual column | 0 | 7.78s | 2,551,296 | 0 |
| Matrix/model bridge | 0 | 1.59s | 2,379,648 | 0 |
| Inverse/evaluation/nonzero bridge | 0 | 1.20s | 2,324,848 | 0 |
| All final new Lean targets, sum/max | 0 | 158.67s | 2,830,420 | 0 |

The final cache contains 170 objects: 124 unchanged predecessors, two
generic leaves and 44 generated files. Eighty-three public evidence
artifacts plus their hash manifest retain the source checks, per-target
results and superseded attempts. The 481 theorem count includes arithmetic
and composition lemmas, not 481 independent security claims.

The generic contraction lemmas compile first, followed by literal inputs,
the first quotient/column, the final quotient/column, and one inverse row.
Only after those focused targets pass are the remaining leaves and bridges
compiled. The generator's `--check` validates all generated bytes before
aggregation. No package-wide dependency build or historical manifest replay
is launched.

Three integration failures are retained, with their source drafts and logs:

- The initial quotient rewrite did not match a finite-index division under
  a binder. An explicitly indexed shift equality fixes the rewrite.
- The first dot/poly composition used `0+j` and finite numerals where the
  rewrite expected definitionally matching indices. The generator now emits
  the exact zero-offset expression and explicit `Fin` constructors.
- The final bridge lacked a synthesized `Nontrivial M` instance. It now
  supplies a local instance from the checked concrete `0 ≠ 1` fact.

None was a memory failure or an arithmetic counterexample. No recurrence or
memory limit was raised. Failed logs' `sorryAx` entries are failed attempts,
not accepted release proofs. Final proof leaves use neither `native_decide`
nor `sorry`, new axioms, broad `norm_num`, or a full recurrence expansion.
Some successful column leaves retain harmless unused-`ite_true` simp warnings.

Rust is release/offline/locked, two jobs, overflow checks enabled, under
MemoryHigh5G/MemoryMax7G. Lean uses 3G/5G. Both scopes set MemorySwapMax0
and TasksMax128. The retained 4.32 Mathlib workspace supplies dependencies.
All exact commands, revisions, source hashes, exit statuses, wall times,
peak RSS, swap and axioms audits are recorded.

Final source stage:
`/home/dombarker/project-offloads/aspis-r40-generator-20260929-d`.
Final focused Lean cache:
`/home/dombarker/project-offloads/aspis-r40-lean-20260929-f`.
All inherited non-Cargo pins remain unchanged; there are 195 source pins.

```
python3 docs/research/v8-full-view-zk-20260912/tools/check_r40_evidence.py
```

## First remaining source-specific proposition

Lift this nonzero restricted determinant to the retained exact QM31 tower,
then establish usable degree bounds **after the actual source substitutions**
and justify the conditional challenge law needed to bound its vanishing
event. A nonzero formal polynomial may still vanish throughout a restricted
sampler support; this witness is not a substitute for that analysis. In
particular, later alpha/query draws depend on the earlier transcript and
channel-fold beta, and shared-oracle first-hit, rejection and repetition
behavior cannot be replaced with an independent-uniform hypothesis.

Universal source refinement, current H1 compatible-image coverage, posterior
simulation, coherent pre-beta quotient-pair extraction, seed/commitment hops,
visible failures/retries/publication and explicit security losses still need
their separate proofs. This result does not close those gates.

No verifier or protocol path changed. CU is unchanged at
**1,620,236 / 1,621,719**; both actual 1M-cap executions exhaust. Full privacy,
soundness closure and supported-budget execution remain open.
