# Selected copy aliases: explicit collision polynomials

Continuation from `6f1ebbe55fcc6fd008071329d5270aae0521cf9a`. This work
consumes the existing selected 136-link row/layout/balance proofs unchanged.
No Rust, verifier grammar, transcript, production default or main-branch edit.

## Completed deterministic endpoint

The new source-shaped endpoint distinguishes three outcomes rather than
promoting a balance at one sampled challenge into a polynomial identity:

1. Every selected weighted tuple alias holds.
2. A specified nonzero polynomial in lambda vanishes at the sampled lambda.
3. A specified nonzero polynomial in chi vanishes at the sampled chi.

`SelectedCopyAliasCore`, the source-dependent `SelectedCopyAliases`, and
`SelectedCopyAliasQM31` are kernel-checked. The last leaf discharges the
selected-field guards and projects the weighted aliases to the seven actual
transfer amount edges. The 32 retained axiom audits use only `propext`,
`Classical.choice`, and `Quot.sound`; there are no new axioms or `sorry` in
the green results.

The premises remain the literal selected Boolean copy-row residuals, zero
total helper sum, zero inactive helper sum, and all four nonzero slot
denominators on every active row. No valid witness, compiler acceptance,
decoder success, honest trace, or already-correct aliases are assumed.

## Actual polynomials and selected registry

Let S be the public-active subset of the literal 136 links, selected by the
five existing weight kinds and the public variant/append index. Put n=|S|.
The endpoints and all 14 tuple patterns are the existing source definitions,
including their public offsets. Slot values are still computed independently
of public weights; no zero-weight denominator is deleted from the premises.

Each endpoint has the actual 16-limb compression polynomial

```
T_i(L) = tag_i + sum_{j=0}^{15} limb_ij * L^(j+1).
```

The two multisets of these polynomials use precisely the same active set S.
Their characteristic-polynomial difference is a polynomial in a new outer
variable whose coefficients are polynomials in L. `lambdaWitness` is its
leading coefficient. If the two polynomial multisets differ, this witness
is nonzero. If their evaluations at lambda coincide, its evaluation is zero.
Its degree is at most **16*n**. This is one witness fixed before lambda,
not a pairwise union over tuples or a permutation selected after lambda.

At fixed lambda, let p(X) and q(X) be the characteristic polynomials of the
two actual compressed-value multisets. The chi witness is the Wronskian

```
chiWitness(X) = p'(X)*q(X) - p(X)*q'(X).
```

The source rational balance equals p'/p-q'/q away from the explicitly
retained poles, so a zero sampled balance gives a root of this polynomial.
If the value multisets differ and positive integers through n have nonzero
field casts, the Wronskian is nonzero. Its degree is strictly below **2*n**.
Neither its definition nor nonzeroness depends on the sampled chi.

If neither collision alternative occurs, the polynomial multisets agree.
Coefficient zero recovers the tags; coefficients 1 through 16 recover the
tuple limbs. Injective field casts of the actual selected tags then identify
the same link index. The resulting equation is exactly

```
weight_i * (producer_limb_ij - consumer_limb_ij) = 0.
```

Inactive links are not required to have equal tuples. The QM31 leaf
discharges the two field guards using the actual characteristic and tags,
not assumptions about honest proofs. No historical 183-link, 78/75-link or
396430 numerator is used. The coarse n≤136 bound is distinct from a precise
active-link count; no global probability budget is claimed here.

## Reused V7 mathematics, not its registry

The generic Wronskian, characteristic-polynomial and compression-coefficient
proofs are reused from
`AspisFormal/AspisFormal/Pool/V7DeployedCopyLogUpCollisionBounds.lean`, pinned
source SHA-256 `271652eb4d02258cd72605ed5e53034b5266af61efbe702da19232945f51985f`.
They are narrowly ported because that old leaf's full alias/registry closure
is uncached. No old registry specialization or claimed acceptance theorem
is imported. Existing pinned Mathlib dependencies are reused without a cold
build.

The source-dependent leaf uses `SelectedCopyLinkBalance` to connect the
actual row sum, and its endpoint-injectivity theorem to transport every
required row-slot non-pole condition to the active compressed multisets.
The new source predicates remain mathematical field-level descriptions;
optimized Rust selector/pattern/accumulation loop translation is separate.

The proved scalar projection uses source indices 11 through 17,
tags 1124073483 through 1124073489. In a transfer all seven weights are one.
These are the exact cell pairs consumed by `SelectedAmountEndpoint`:

| Producer | Consumer |
|---|---|
| (44,0) | (1008,10) |
| (460,0) | (1010,10) |
| (508,0) | (1012,10) |
| (1008,10) | (1014,0) |
| (1010,10) | (1014,1) |
| (1012,10) | (1015,1) |
| (1014,2) | (1015,0) |

This supplies those exact field-cell aliases on the alias branch of the
new partition. It does not by itself establish the remaining amount
residuals, positivity gate, canonical raw decoding, or the full checked
payment validator. The field-cell projection is not a claim that the
existing amount theorem has been instantiated against a parsed Rust trace.

## Causality and remaining acceptance bridge

For a probabilistic application, the table supplying these tuple polynomials
must be a C1 candidate fixed before lambda, or one member of a mathematical
candidate family fixed before lambda with its selection cost separately
justified. Being fixed only before gamma, or being obtained from a late
C2-dependent tuple, is not sufficient. The public active
set must likewise be fixed by the authentic caller context. Under those
conditions the lambda witness is fixed before lambda. After lambda, the
chi witness is fixed before chi. Helper responses can depend on preceding
challenges; their local residual and boundary properties are explicit
premises, not assumed consequences of sampled acceptance.

These deterministic root alternatives are not conditional uniform-sampling
theorems. The actual ideal law, candidate-family selection/coverage, all-slot
pole events, source/semantic enforcement and resource-bounded Fiat–Shamir
lift remain separately necessary. In particular, filtering to active-link
multisets does not justify ignoring poles of inactive or empty source slots.

The proof body remains 40,282 bytes. There are no new messages, verifier
operations or privacy claims. No proving, SBF, transaction CU, deployment or
extractor-runtime measurement was performed.

## Focused evidence

Scope: `/home/dombarker/project-offloads/aspis-linear-factor.8SUGGL`, runner
`run_linear_factor_nuc.sh`; Lean 4.32.0, -j1/-M9500, MemoryHigh 8 GiB,
MemoryMax 10 GiB, MemorySwapMax 0, CPUQuota 200%. Borrowed-source pin
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`. Native packages are a pinned-cache
boundary, not a fresh replay. All runs retain exact source snapshots, logs
and per-run manifests under `experiments/`.

| Attempt | Exit/status | Wall | Peak RSS (KiB) | Swaps |
|---|---|---:|---:|---:|
| Core v1 | 1: missing narrow GCD/Splits imports | 8.15 s | 2,172,116 | 0 |
| Core v2 | 0: twelve standard-only audits | 1.64 s | 2,193,508 | 0 |
| Aliases v1 | 1: Boolean/definition simplification glue | 1.32 s | 2,181,808 | 0 |
| Aliases v2 | 0: eleven standard-only audits | 1.37 s | 2,193,368 | 0 |
| QM31 v1 | 1: broad singleton source-lookup simp loop | 3.31 s | 6,667,476 | 0 |
| QM31 v2 | 0: nine standard-only audits | 3.42 s | 6,694,940 | 0 |

The Core v1 instance search exhausted its heartbeat budget after a missing
GCD instance; it was not rerun with higher limits. Adding the exact cached
`Polynomial.Content` and `Polynomial.Splits` imports corrected the dependency
gap. The retained failed logs' diagnostic `sorryAx` entries are not claimed
proofs. Aliases v2 changes only the Boolean branch and named-definition
simplification glue. QM31 v1's broad concrete source lookup was replaced
by a seven-entry, field-free metadata certificate followed by symbolic
field lemmas. Neither recursion nor memory limits were raised. All final
sources and compiled outputs are frozen; no unchanged suite was replayed.

The literal runner command for each focused check is:

```sh
bash /home/dombarker/project-offloads/aspis-linear-factor.8SUGGL/run_linear_factor_nuc.sh \
  /home/dombarker/project-offloads/aspis-linear-factor.8SUGGL TARGET TAG
```

The three final `(TARGET, TAG)` pairs are:

- `SelectedCopyAliasCore`, `selected-copy-alias-core-nuc-v2`.
- `SelectedCopyAliases`, `selected-copy-aliases-nuc-v2`.
- `SelectedCopyAliasQM31`, `selected-copy-alias-qm31-nuc-v2`.

Each v1 and v2 has a retained `TAG.log`, `TAG-manifest.json` and
`TAG-source.txt`. The logs include the literal Lean command, exact cgroup
limits, source/output hashes, before/after overlay checks and axiom output.
Runner SHA-256:
`ff4db59289e0f873ab2892ebf6f8dcf294966ec42a457f3cff0c09bec01093bb`.

Core source: `157dfc32c9735108121aa468cb25c2a9cf58c1c3015b1150ea14957e60c90749`.
Core output: `59c824b2e45e0262d85e5fea8abb57d7831f97e42823a4bf28153988d98bba0a`.
Core green log: `55ac0f63a0c3c9044c06beb0e5723091a6c9f5f821ba63c4bf699c0da1a41fe3`.
Aliases source: `c298d4879f936a26fb943d6f0d39b4135fe4e943d37ff0d0b738df61fdbae902`.
Aliases output: `5e417b1d5b2a3c5dc38dbc670d304e85ba397745acbb0e4f8723bf5296d917fa`.
Aliases green log: `665745b660bc2f6ff393bbcfbdbbc760d7ddeb06fd0c038a5137da1ff28ac95a`.
QM31 source: `a82ddcae4dffa1c8c5e9c3e6a0b65a9a385f1cce425b5eb2d17dde362594e3cb`.
QM31 output: `4d2d458e818a81eaba47fa7eb47abf2e22ef7ff18b9074c505eb282528a65e9b`.
QM31 green log: `433f0bb1832098ca5c75e90654f19ee75f7c825e85d7688c40d1806997a6d3ef`.
QM31 v2 manifest: `8c46eb580e7958bdb87df03e9e37c2a11bc1aef6961557a43c1bbed963072667`.
No commit or push was made by the subagent.
