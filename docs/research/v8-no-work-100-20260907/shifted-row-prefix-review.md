# Shifted rows: constructing the ordinary prefix after affine transport

Checkpoint: `15e73e9fdf529a0d0ab46353b98bccaf029bf4f5`.
[`ShiftedRowPrefix.lean`](experiments/ShiftedRowPrefix.lean) connects four
fixed original functionals and their actual scalar claims to the
[`FirstImageDiscrepancy.Before`](first-image-discrepancy-review.md) constructor.
The new implication includes the affine interpolant subtraction and linear
chord transport; it does not assume a supplied transport/dot equality or
inactive exactness.

## Constructed interface

`Rows` contains four original coefficient covectors `w_j`, four claims `c_j`,
a linear reconstruction map `L`, interpolant `I`, reference quotient
coefficients `Q`, quarter constant, and image coefficients `b,c`. Every one
of those inputs is fixed before kappa. `ell_j` is constructed as the actual
coefficient dot with `w_j`.

The ordinary functional and corrected scalar are

```
ell_kappa = ell_0 + kappa*ell_1 + kappa^2*ell_2 + kappa^3*ell_3
claim_kappa = c_0 + kappa*c_1 + kappa^2*c_2 + kappa^3*c_3
                - ell_kappa(I).
```

The transported covector is **constructed**, coordinate by coordinate, as

```
W_kappa[i] = (ell_kappa composed with L)(coordinate_vector_i).
```

`reify_dot` proves symbolically in arbitrary dimension that its dot with any
coefficient vector is the represented linear functional. This closes the
generic transpose interface without a caller-supplied equality. It is a
mathematical construction, not a proposed 1,024-basis-vector computation for
the on-chain verifier.

`Rows.before kappa` installs `W_kappa`, `claim_kappa`, and the unchanged
`Q,quarter,b,c` into the actual mathematical pre-image prefix. Reusing
`ClaimTransport.corrected_prepare_discrepancy`, the theorem `before_prior`
derives

```
(Rows.before kappa).prior = P(kappa)
P(X) = e_0 + e_1*X + e_2*X^2 + e_3*X^3
e_j = c_j - ell_j(L(Q)+I).
```

The error coefficients are actual original-row dot errors, not fields named
`error` accompanied by an assumed correspondence. `error_coeff` identifies
each coefficient, `error_degree` gives degree at most three, and
`error_nonzero` proves nonzeroness if any of the four errors is nonzero.
The inactive row is `e_0`: it remains present with power zero and is never
assumed exact. `before_E1`, `before_E2`, `before_quarter`, and
`before_referenceQ` make the inherited image and reference interfaces
explicitly independent of kappa.

This consumes the existing corrected affine transport theorem and the
V7-consumed finite coefficient/dot representation. It adds no new probability
term and does not re-prove the earlier abstract row-game bound. A causal
composition may now consume the derived cubic, rather than assuming its
coefficient interpretation.

## Selected source audit

The selected path is `structured_weights.rs::prepare`, not the obsolete
dense transcript path in the older diagnostic callback. Its source SHA-256
is `06befd20c084234ce1afa2d7cf3612a12370fdb0e98e95db30d89cf245b51089`.

| Source operation | Mathematical interface |
|---|---|
| Line 125 absorbs `w.v[358]`, then derives nonzero kappa | Inactive scalar is fixed before kappa |
| Line 126 constructs `[kappa,kappa²,kappa³]`; grouped inactive masks retain scale one | All four powers are `[1,kappa,kappa²,kappa³]` |
| Lines 139–143 add the three gamma-batched point-row claims with those powers | `c_0+kappa*c_1+kappa²*c_2+kappa³*c_3` |
| Lines 144–150 construct interpolant and chord from already fixed OOD points/answers and gamma | `I,L,b,c` depend on pre-kappa information, although these computations occur later in the Rust control flow |
| Lines 160–162 subtract `iv[0]*entry(0)+iv[1]*entry(h_index)` | `ell_kappa(I)` for the source interpolant supported at coefficient 0 and coefficient 2 (`x`) or 1 (`y`) |
| Structured chord transport computes only required terminal functionals | The represented covector is `ell_kappa composed with L`; concrete optimized-kernel correspondence remains a separate theorem |
| Lines 163–172 bind the compact functional description and corrected scalar, then derive tau | No unchecked prover-supplied functional hash or moved image challenge |

The original point functionals, their exact source selectors/grouped masks,
the concrete chord reconstruction matrix `L`, and the sparse interpolant
coefficient representation still require their literal source
instantiations. This leaf proves the transpose and affine **interfaces**,
not that every optimized Rust instruction implements them. The selected
fused-row kernels remain covered by their existing algebraic/differential
evidence; no unchanged tests were rerun.

The reference `Q` and support set used by any subsequent game must be fixed
before kappa for this cubic argument. A post-kappa chosen anchor cannot be
substituted retrospectively. This requirement is compatible with an anchor
constructed earlier from the received words/previous challenges, but that
construction and its coverage must actually be proved. No decoder membership,
image validity, exact global received polynomial, witness, or acceptance
premise appears in this constructor.

## Focused evidence

From the research worktree, with fresh log names:

```sh
bash docs/research/v8-no-work-100-20260907/experiments/run_shifted_row_prefix.sh \
  claim docs/research/v8-no-work-100-20260907/experiments/shifted-row-claim-cache-v1.log
bash docs/research/v8-no-work-100-20260907/experiments/run_shifted_row_prefix.sh \
  leaf docs/research/v8-no-work-100-20260907/experiments/shifted-row-lean-v1.log
```

The existing `ClaimTransport` source had no importable olean in the research
or inspected temporary caches. Its one focused export was therefore a
missing-artifact replay, not a new claim or an unchanged full regression.
Do not repeat that export when the pinned artifact exists.

Both runs used the exclusive local compile slot, `lean -M7000`, and an
independent 7-GiB descendant-RSS guard. The runner resolves `lake env` before
starting the bounded Lean process, records the imported repository closure,
matches imported sources against the checkpoint and both worktrees, and
checks unchanged source/olean provenance afterward. No dependency build,
SBF build or concurrent Lean job was launched.

| Log under `experiments/` | Exit | Wall seconds | Peak RSS bytes | Swaps | Audit |
|---|---:|---:|---:|---:|---|
| `shifted-row-claim-cache-v1.log` | 0 | 2.26 | 2,882,355,200 | 0 | Six existing declarations, standard axioms |
| `shifted-row-lean-v1.log` | 0 | 11.84 | 5,654,691,840 | 0 | Twelve declarations, standard axioms |

The new leaf passed on its first compilation. All printed axiom sets are
subsets of `propext`, `Classical.choice`, `Quot.sound`; no `sorry`, new axiom,
large concrete normalization or increased resource/recursion limit is used.
The recorded read-only main revision was
`d851f36bc0ee41459156e125aaa04e4a0941ac70`.
Lean 4.32.0 and Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997` are pinned
in the evidence.

SHA-256 pins:

```
ShiftedRowPrefix.lean
c5ef1ae4a50c6f4dd216ec61f8cd0aa1f46a74e91d11ee73bb1052f6eab1b303
ShiftedRowPrefix.olean
58def1481f0a896ae0cbb210c52a682ef81ed1366e9fb4996188edf18415fa9f
ClaimTransport.lean
bc938d4a2765e0a697edc701ac8c2e3aba84a07ebf95bfe3d1fd47e97d693e08
ClaimTransport.olean
6cddaad7b63f0cf8b51d0b6f9c13d67861795374977972f3e05907dcf798155f
run_shifted_row_prefix.sh
9a1e030dd3fa9474776fd8b39dd7eabeba447d6ddd9a70fb916ac92766310b8f
```

## Decision and unchanged costs

The ordinary-row-to-image-prefix gap is smaller: both the shifted scalar
polynomial and its affine transported covector are constructed and their
discrepancy relation is proved. The
[causal ordered row/image composition](causal-row-continuation.md) is now
complete for its stated pre-kappa image-valid anchor/support regime. It
derives the q22 ceiling
`25/(k-1)+24/k+choose(B+255,22)/choose(T,22)` from this constructed cubic and
the actual compact relation/query game, with `k=|QM31|`, `B` the corruption-set
cardinality and `T=262144`. The tau discrepancy is constant for
an image-valid reference; no image-challenge conditioning or extra tau-root
charge is introduced. All four relation repairs are counted once.

The fixed-prefix and anchor-support hypotheses remain explicit. This does
not establish global recovery, payment knowledge, authentication/source
refinement, full-view privacy or a resource-bounded Fiat–Shamir theorem;
accepted no-anchor and correctly bound but unrecovered regimes remain
separate obligations.

Only new research proof/runner/evidence/report files were added. No protocol
or verifier operation changes, extra proof fields, new CU measurements or
prover benchmarks arise here; the body remains 40,282 bytes. No grinding
credit is introduced, and relation-repair events must still be counted once
by the eventual composition.
