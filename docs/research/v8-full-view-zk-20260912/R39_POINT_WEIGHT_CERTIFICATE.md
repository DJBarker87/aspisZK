# R39: certify the algebraic witness's transported point weights

Parent `d7767ea379469c4f619d28588200fa8715bf6383` (R38).
Branch `research/v8-r39-point-weight-certificate-20260929`.

**Result:** all 782 new theorem declarations compile with standard axioms
only, and the offline evidence gate passes. This closes the concrete
point/code/chord-weight part of the existing algebraic specialization,
not its residual matrix determinant or the full privacy theorem.

This stage connects literal statement points, T163 dual weights and
chord-transposed weights to `ResidualModel.pointWeight`. It extends R38's
root/shift certificate for the **same R37 algebraic witness**; it does not
substitute an invented transcript for either retained actual source prefix.

The witness still uses z = [2,...,11], kappa = 5, alpha = 7, u = 2, v = 3
and roots = [1,...,22]. This stage uses its normalized chord (7,5,-5), not
the rational chord divided by 25. R37's determinant scaling theorem remains
the bridge between those chords under its explicit nonzero premises.

## Exact statements and source checks

The literal arrays inhabit `ZMod 2147483647`, with half = 1073741824.
The three point definitions retain the actual successor carry and the
third point's coordinate-6/7 flip. The dual code weights are

```
tensor(point_i, order[j]) - inactive[j] * tensor(point_i, 1023).
```

Here `inactive[j]` is the R36 pin at the **mapped original coordinate**,
not a flag indexed incorrectly in the code basis. No balancing term is
discarded. For each r < 108 the transported weight is the full model sum
over j < 111 of this code weight times `chordEntry ... r j`.

The generated proof stages contain:

- 30 point-coordinate checks;
- 333 code-weight coordinate checks;
- 108 chord support-row certificates;
- 324 transported-weight coordinate checks;
- three final point-weight bridges applying a generic composition theorem.

The generic theorem takes independently certified point, code and chord
stages. The final concrete theorems discharge every one of those premises:

```
pointWeight ResidualPins.order ResidualPins.inactive
  half 7 5 (-5) z i r = weights_i[r]       (i=0,1,2; r<108).
```

The optimized Rust generator independently checks the pinned constructor's
2,048 order/inactive entries, all 30 source statement-point coordinates,
3,072 source tensor coordinates, 333 source dual-code coordinates and
324 source chord-transpose coordinates. It checks that every exported
value has only a canonical M31 limb. Omitting the pivot correction changes
318 of the 324 low weight entries; this negative control is retained.

These source tests are **finite executable comparisons**, not a universal
Rust-to-Lean refinement theorem. The final Lean bridges prove equality to
the explicit R36 model, and do not silently promote those comparisons into
universal source semantics or a source challenge-distribution theorem.

## Sparse normalization, including the failed preflight

The initial one-cell chord test attempted to normalize the entire 111-term
sum and hit Lean's recursion-depth limit in 1.02s. The failed source and
log are retained. It was not rerun with a larger recursion or memory cap.

`PointWeightCertificate.sparse_sum` instead proves a generic finite-sum
restriction from a certified zero-outside-support premise. The generator
computes each row's candidate support, then emits a Lean proof checking
every excluded index against `chordEntry`. The transported-weight leaves
apply that named theorem before evaluating the small surviving sum.
Thus an incorrect generated support is rejected by the kernel; it is not
trusted just because Rust produced it. Each support row is reused across
the three point channels. The replacement preflight passes in 2.04s.

Every code/weight chunk has at most 12 equations. Points and code values
are literal prior-stage data, so the chord stage never recomputes nested
point carries or tensor products. The final bridge composes named
theorems instead of unfolding those earlier calculations.

No `native_decide`, `sorry`, extra axiom, `norm_num`, recursion-limit
increase or full root-recurrence expansion is used in the final proof.
The retained failed preflight does contain Lean's error-generated
`sorryAx` audit; it is explicitly a failed result, not a release proof.

## Verification and evidence

| Focused work | Exit | Wall | Peak RSS KiB | Swaps |
| --- | ---: | ---: | ---: | ---: |
| Final optimized generator compile | 0 | 19.71s | 517,840 | 0 |
| Final generic composition/sparsity lemmas | 0 | 1.02s | 2,258,644 | 0 |
| Dense one-cell preflight (retained failure) | 1 | 1.02s | 2,255,036 | 0 |
| Replacement sparse preflight | 0 | 2.04s | 2,416,840 | 0 |
| Final three-channel bridge | 0 | 2.60s | 2,560,452 | 0 |
| All final new Lean targets, sum/max | 0 | 206.58s | 3,129,308 | 0 |

The final cache contains 124 objects: 53 unchanged predecessors, the
generic leaf and 70 generated files. There are 782 audited new theorems,
including the support certificates, preflight and composition statements;
this is not 782 independent privacy results. Ninety-five evidence artifacts
plus a hash manifest retain the successful results and superseded attempt.

The generator emits 70 files and runs `--check` before Lean aggregation.
All inherited non-Cargo source pins are unchanged; the new source stage
has 194 pins. Release Rust uses the cached workspace, two jobs, offline
and locked dependencies, and overflow checks enabled.

The generic leaf is compiled first. After the sparse fix it is recompiled,
then literal data, the three point theorems and the sparse preflight are
compiled before the remaining chunks and final bridge. Only matching
source-hash/toolchain predecessor objects are reused. No old full
regression, cold dependency build or unchanged SBF run is performed.

Source stage:
`/home/dombarker/project-offloads/aspis-r39-generator-20260929-b`.
Final Lean workspace:
`/home/dombarker/project-offloads/aspis-r39-lean-20260929-e`.
Rust scope: MemoryHigh5G/MemoryMax7G. Lean: 3G/5G.
Both use MemorySwapMax0 and TasksMax128. Another user's existing 8G scope
was inventoried; the combined maximum reservation remained at most 20G
on the 62GiB host. No unrelated job was stopped or altered.

Per-target exit status, exact command, source SHA, base revision,
wall time, peak RSS, swap and axioms audits are retained under
`evidence/r39-point-weight-certificate`, including the failed preflight.

```
python3 docs/research/v8-full-view-zk-20260912/tools/check_r39_evidence.py
```

## First remaining proposition

Combine R38's certified root/shift arrays with these point weights to
certify all 169 entries of the selected 13-by-13 residual minor, then its
invertibility. The quotient arrays must be connected to `quotient`, and
each ordinary/G coefficient must retain `polyCoeff`'s [0,3,2,1] convention
and quarter factor. A proof that an unrelated exported matrix is invertible
does not establish the required `normalizedMinor` specialization.

After specialization and exact-field lifting, use
`SourceResidualPolynomial.determinant_evaluation` to establish polynomial
nonvanishing. Even that does not prove an actual shared-oracle exception
bound. Degree accounting, universal source correspondence, H1 coverage,
posterior-preserving simulation, pre-beta extraction, seed/commitment hops,
visible failures/retries/publication and explicit losses remain separate.

No verifier/protocol path changed. The selected CU remains
**1,620,236 / 1,621,719**, and both actual 1M-cap runs exhaust. Full privacy,
soundness closure and supported-budget execution are not claimed complete.
