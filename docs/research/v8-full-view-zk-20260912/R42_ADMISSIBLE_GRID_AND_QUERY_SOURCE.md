# R42: admissible-grid bound and exact query-source checks

Parent `10751450ff23b5c2316b8e220f95a65f6b875ea5` (R41).
Branch `research/v8-r42-admissible-grid-bound-20260929`.

**Result:** six Lean theorems compile; the actual query-root map has been
checked exhaustively at all 262,144 indices; 69 focused source-control
cases pass. The conditional finite-grid bound is proved, but it is not a
law for the source shared oracle and is not a full privacy theorem.

No verifier, protocol, wire format, mask, or assumption changed. No SBF
replay: the selected R27 endpoint remains 1,620,236 / 1,621,719 CU, and both
retained 1M-cap executions exhaust. R21 remains retired.

## What is formally proved

`AdmissibleGridBound.lean` imports the cached Mathlib Schwartz–Zippel proof,
not an assumed Schwartz–Zippel interface. It proves:

1. For a nonzero polynomial of total degree at most d, on the product grid
   `G = ∏ Sᵢ` with every `|Sᵢ| ≥ m > 0`, the uniform zero fraction is at
   most `d/m`. The sets may differ between coordinates. The proof bounds
   each supported monomial's weighted degree; it does not pay an extra
   factor equal to the number of variables.
2. For a nonempty admitted subset `A ⊆ G`, a uniform bad fraction bounded
   by b on G becomes at most `b / (|A|/|G|)` on A. No conditioning cost is
   dropped. The finite-count statement makes no claim that the actual
   execution is uniform on A.
3. Combining these gives the corresponding conditional polynomial bound.

`QM31AdmissibleGrid.lean` instantiates both bounds with the exact R41
36-variable QM31 determinant and its proved degree bound 1,105. It also
retains the implication from a nonzero evaluated determinant to
surjectivity of the selected residual map.

This does not replace a proof about all original compatible equations or
the posterior-preserving simulator. The same 13-by-13 selected minor is
used. Its singularity need not imply failure of the full system, much less
a published attack.

## Exhaustive actual-source root support

`r42_root_support.rs` calls the pinned
`selected_circle_fiber_points_shared(20, indices)` on **every** index in
`[0, 2^18)`. It checks the source's three-window table implementation
against an independent sequential circle-group walk using ordinary u64
modular arithmetic, not the source field-reduction kernels or its tables.

The reference uses the pinned generator `(2, 1268011823)`, initial exponent
`2^10`, step `2^12`, and the full 18-bit reversal. The generator order is
checked. For every point it checks both coordinates, the circle equation,
and the residual root `2*x² - 1`. All roots are canonical, distinct, and
different from 1. Thus this executed source instance has exactly 262,144
root values, not `|QM31|` root values.

The ordered little-endian root-list SHA-256 is:

```
e417c33d590558595f5a27abc44cfe9fc6985b02bce7d17fcc974025033ba4a1
```

Negative controls retain an inserted duplicate, an incorrect unreversed
index order (261,632 mismatches), and two out-of-range indices. Repeated
valid indices deliberately return the same point: distinctness comes from
the sampler, not a deduplicating root-map API.

This is an exhaustive optimized executable check of the finite source map,
**not** a Lean source-refinement theorem. The evidence additionally records
the unchanged core `build.rs` that generates the tables; it was not among
the older 195 selected source pins. The generator is identical in the
control and both new stages. Its hash is a supplemental pin, not a silent
claim that it was covered by the older manifest.

## Source control: keep the extra detection block

The retained V5 `QuerySamplerControl` already documents the subtle block
behavior; R42 does not claim to discover or change it. The current source
checks completion at the **start** of an inner word iteration. Consequently,
for first success at candidate h:

```
22 ≤ h < 64:  consumed blocks = floor(h/8) + 1
h = 64:       consumed blocks = 8
failure:      consumed blocks = 8
```

Success at 24, 32, 40, 48, or 56 therefore squeezes and advances through
one extra block solely to detect completion. The extra squeeze answer is
unused by the query output, but its oracle read and the state advance must
remain in a source-faithful shared-oracle experiment.

`r42_query_control.rs` exercises the unchanged source with an explicitly
scripted hash backend. It checks:

- 43 first-success positions, 22 through 64, including masked high bits;
- exact ordered outputs, every squeeze/advance address, and resulting state;
- the next squeezed block in all 43 success cases;
- 21 exhausted schedules retaining 1 through 21 distinct values;
- five early-return/error cases, including invalid bounds and a zero cap.

The backend is deliberately **not** a random oracle. These are operational
source tests, not statistical evidence of uniformity or a SHA security
claim. No production validation or negative regression is removed.

## Why the conservative bound does not finish privacy

For orientation only, consider a genuinely independent product experiment
where the smallest coordinate support is the N=262,144 root set. The new
theorem yields `1105/N`. Conditioning **only** its 22 root draws to be
distinct gives the exact counting expression

```
(1105/N) / ((N·(N−1)·...·(N−21))/N^22)
≈ 0.00421895666634.
```

This is a coarse upper bound for a selected determinant in that ideal
experiment. It is **not** a measured frequency, a lower bound, a source
privacy-loss estimate, or evidence that approximately 0.42% of proofs leak.
The displayed number does not include OOD restrictions, shared-oracle
first hits, observer queries, or publication conditioning. It cannot be
used as the release privacy bound. In particular, replacing N by `|QM31|`
would be unjustified.

The retained `V5BoundedQuerySamplerUniformity` supplies equal-fibre uniformity
for the successful output of an **ideal finite independent-draw** bounded
sampler. Its generic parameters can represent 22/262144/64. It does not
identify the actual transcript with that experiment. The retained R17
`AdaptiveOracle` theorem requires the next oracle address to be unread in
the complete relevant trace; R42 has not discharged that source premise.
Output uniformity conditioned on sampler success also does not establish
uniformity conditioned on later proof acceptance or publication.

## First remaining proposition and next route

The immediate source-specific obligation is a joint-law refinement for the
actual causal prefix: fresh squeeze/advance addresses (or explicit
first-hit/collision losses), canonical QM31 rejection, nonzero/OOD sampling,
the ordered 22-of-262144 query schedule, the exact detection-block state,
and observable bounded failures. It must retain both channel coefficients
before beta, alpha afterward, and Final256 before queries. Retry and
publication conditioning cannot be silently included as free events.

Even closing that law would leave the conservative bound above too weak
for a cryptographic closure. A concrete stronger algebraic target is:

> For every distinct 22-tuple of actual source roots, after fixing those
> root coordinates, the remaining 14-variable residual determinant is
> nonzero; alternatively, supply a covering family of minors with a proved
> full-image exception bound if this particular minor does not suffice.

R40's one algebraic root tuple `1,...,22` does not prove that statement.
Nor does the exhaustive root-map check test these determinant
specializations. With a justified joint sampler law, a root-uniform
nonvanishing result could permit a large-field bound on the other
coordinates. It remains a proposition to prove, not a new assumption.

Full Rust/model correspondence, joint H1/G coverage, adaptive posterior
retention, coherent pre-beta extraction, seed/commitment hops, and
retry/publication accounting remain separate release obligations. No full
privacy, soundness closure, or supported-budget completion is claimed.

## Compilation and evidence

| Target | Exit | Wall | Peak RSS | Swap |
| --- | ---: | ---: | ---: | ---: |
| `AspisV8R19/AdmissibleGridBound.lean` | 0 | 1.09 s | 2,079,696 KiB | 0 |
| `AspisV8R19/QM31AdmissibleGrid.lean` | 0 | 1.94 s | 2,452,596 KiB | 0 |
| Release root-check compilation | 0 | 19.16 s | 517,424 KiB | 0 |
| Exhaustive root check | 0 | 0.01 s | 7,744 KiB | 0 |
| Release control-check compilation | 0 | 18.72 s | 518,000 KiB | 0 |
| Scripted control check | 0 | 0.00 s | 1,936 KiB | 0 |

All six new theorem audits use only `propext`, `Classical.choice`, and
`Quot.sound`. One initial Lean annotation/type mismatch is retained with
exit 1 and corrected locally; no resource failure or cap increase occurred.
Lean used the existing 4.32 cached workspace, 3G/5G/no-swap limits. Rust
used release, locked/offline, two build jobs, overflow checks enabled,
5G/7G/no-swap limits. Time was spent compiling small source targets, not
performing dense elimination. No old regression or SBF build was repeated.

The 21-artifact manifest and offline gate are under
`evidence/r42-admissible-grid` and `tools/check_r42_evidence.py`. The final
stage has 197 selected pins: the previous 195 are unchanged except for
additive host-only Cargo binary entries, plus the two new test binaries.
The extra build-script pin is recorded separately. The evidence gate passes.
