# Ordered post-query functional: a constructed deterministic interface

Checkpoint: `5e26df14ad5fc674d5ea43d02431f1dc9ef682fa` on
`research/v8-no-work-100-20260907`. This adds mathematical source-shaped
interfaces; it does not change Rust, the transcript, the proof grammar, or
production. No additional CU or proving benchmark was run.

## What is now derived

[`PostQueryFunctional.lean`](experiments/PostQueryFunctional.lean) constructs
the 256-dimensional functional after the first fold and the ordered query
injection. The incoming ordinary functional is arbitrary, with the literal
image terms at indices 1023, 1022 and 1021 added before the dual fold. The
reference quotient `Q` is an explicit analysis object. The received folded
word remains an **arbitrary function**, not an assumed polynomial.

Write `Q* = primalFold(alpha0,Q)`, `W* = dualFold(alpha0,W_image)`, and let
`c*` be the evaluation of the actual compact first response. For the final
coefficient vector `F`, ordered positions `x_j`, received values `R(x_j)` and
natural-line basis `N_i`, the constructor uses

```
W_rho(i) = W*(i) + sum_j rho^(j+1) N_i(x_j)
c_rho    = c*    + sum_j rho^(j+1) R(x_j)
r_j      = Eval(F,x_j) - R(x_j).
```

The new `post_discrepancy` theorem derives, rather than assumes,

```
c_rho - dot(W_rho,F)
  = (c* - dot(W*,F)) - rho * sum_j r_j rho^j.
```

Both source updates are additions; the minus sign in the discrepancy is
derived from scalar-minus-dot. Query ordinal `j` is preserved throughout.
No correct-prior or vanishing-residual premise is used.

Additional derived interfaces are:

| Interface | Newly checked statement | Remaining boundary |
|---|---|---|
| Actual polynomial/four-slot fold | `circleFibre_fold` evaluates the natural circle polynomial in order `(x,y),(x,-y),(-x,-y),(-x,y)` and constructs the normalization inverses from nonzero `x,y`; its fold equals evaluation of the actual 256-coefficient primal fold at `2*x^2-1` | Applying it to committed quotient openings still requires the component/chord/division bridge; arbitrary received words are not declared polynomial |
| Final difference | The polynomial `EvalPoly(F)-EvalPoly(Q*)` has degree at most 255 and is zero iff the coefficient vectors are equal | This does not prove that a suitable reference `Q` exists |
| `same_prior` | If that difference is zero, the actual prior equals the compact first-response discrepancy against the reference convolution | `Prefix` is a post-alpha0 snapshot; proving that response0 preceded alpha0 remains the preceding causal constructor's task |
| `zero_iff` | The residual array vanishes iff `difference(x_j)=noise(x_j)` for every ordered query, where `noise=R-Eval(Q*)` | No bound on this noise's support is supplied or inferred |
| Exact-polynomial specialization | If the received function really is `Eval(Q*)`, residual zero means the difference vanishes on the scheduled positions | The caller must establish that exact-function premise before using this specialization |
| Three compact tail rounds | `tail` constructs `JointImageGame.Rounds` from `RawRounds`, transporting along the derived discrepancy identity; `tail_acceptance_iff` derives the terminal-zero equivalence | Scalar/weight/vector inputs are mathematical field objects, not a translated byte parser or LLVM program |
| Concrete query domain | Exact stored log18 coordinates are injective, equal to `2*x^2-1` for the source slot-zero fibre point, and stay distinct under an ordered injection | Actual bounded sampler and Fiat–Shamir law are separate interfaces |

Thus the caller no longer supplies `same_prior`, `zero_iff`, a final-degree
certificate, or a query-injection/terminal equality for this functional. The
remaining anchor existence/support, authentication and source correspondence
obligations cannot be replaced by these identities. In particular, this does
not close the image-valid non-polynomial recovery event or payment extraction.

## Reused V7-consumed algebra and exact geometry

The task reuses the earlier formal development, including files named V5/V6
that the V7 selected theorem already consumed:

| Retained source | Reused content |
|---|---|
| `V7ExactOneFoldDomains` | Exact bit-reversed log20 fibres/log18 stored coordinates, injectivity, and the doubled-coordinate bridge; not a domain inferred from cardinality |
| `V5FriConcreteEncoderApplicability` | Natural-line coefficient evaluation as a dot product, degree bound, and coefficient injectivity |
| `V5FriInitialCircleEncoderIdentity` | Even/odd natural circle coefficients and their four lane identities |
| `V5FriConcreteEncoderCommutation`, through the pinned import closure | Four-slot normalized circle fold and the primal coefficient lane combination |
| `V5FriRelationCandidateBridge`, `V6RelationFold`, `V6TranscriptRelationGrammar` | Honest convolution/dual-fold identity and the six-field compact response, via the previously proved `OptimizedRelationRefinement` constructor |
| `ImageCallbackInterfaces.query_injection` | Generic finite-sum injection identity, now instantiated at the actual natural-line evaluation functional |

No q16 sampling, V7 work multiplier, generic compiler-round multiplier, or
previous global error inventory is imported. These are deterministic facts;
they supply no new independent error term and do not re-prove the restricted
118.415-bit image game.

## Source audit and query order

The inspected Rust files are unchanged at the checkpoint:

| File | SHA-256 |
|---|---|
| `experiments/relation_callback.rs` | `d7a6eff3f93e36a11525818f3fd672b1e60f71c1bf48138292cdc636ef3ba615` |
| `experiments/quotient_fold.rs` | `65dcdc718b9e2e061d48fbe3de1ca6d69733f9156d1b78c9e2fed1e04a4df76d` |
| `crates/aspis-core/src/sumcheck.rs` | `7e12acf033a9c309a836dcb1c334c69932e15b97407613b3968f8e1c53787ead` |

`relation_callback.rs:119` derives final256, the final nonce, the ordered
q22 schedule, and then rho. `opened_values_prepared` retains record/query
order for combined values, fibre points, inverses and returned quotient
folds. Its independently sorted authentication entries do **not** sort the
query array. `inject` at line 270 starts at rho, repeatedly multiplies by rho,
adds the line-batch functional, and adds its opening dot to the carried
scalar. `sumcheck.rs:835` evaluates that line batch with the low coefficient
index bits and successive `x -> 2*x^2-1` factors. These match the modeled
natural-line weight expression.

The selected optimized `quotient_fold.rs` expands the same normalized
butterfly. Its existing production-field differential evidence is not rerun
here. The new field-level theorem uses the reference normalized fold; it is
not an Aeneas translation of the optimized mixed-width kernel or a machine
range proof for that kernel. That distinction remains in the source boundary.

There is a genuine interface issue in the earlier game: its residual/tail is
indexed only by an unordered `Finset`, whereas the source's rho powers and
later responses may depend on query order. This leaf deliberately accepts
`Fin q -> K`, with no silent sorting. The now-completed
[`OrderedQueryGame`/`OrderedPostQueryGame` bridge](ordered-post-query-review.md)
constructs the uniform ordered post-query game from this functional and proves
its conditional bounds. It preserves all first-occurrence orderings rather
than selecting a sorted representative. The concrete domain theorem supports
`Fin q ↪ Fin 262144`. Actual bounded-sampler/Fiat–Shamir correspondence and the
causal pre-alpha0 constructor remain open.

The optimized public-functional transcript is still the compact 545-byte
description documented in [optimized-relation-reuse.md](optimized-relation-reuse.md),
not the obsolete 16,384-byte expanded hash. This continuation adds no absorbs,
challenge calls, claims or nonces. All existing nonce/retry/prequery selection
powers remain for the later resource-bounded Fiat–Shamir analysis.

## Focused evidence and reproduction

Only cached focused leaves ran, with an exclusive local compile slot and
`lean -M7000`. The main worktree was read-only. Its recorded revision during
these runs was `94459d0f9700388431c26c1261fbfa6974118af0`; the runner checks
matching imported source hashes in **both** worktrees and cached olean hashes
before compiling, rather than trusting that moving revision as provenance.
Lean is 4.32.0 (`8c9756b28d64dab099da31a4c09229a9e6a2ef35`) and Mathlib is
`81a5d257c8e410db227a6665ed08f64fea08e997`.

From the research worktree, using fresh output-log names:

```sh
bash docs/research/v8-no-work-100-20260907/experiments/run_post_query_functional.sh \
  interface docs/research/v8-no-work-100-20260907/experiments/post-query-interface-v1.log
bash docs/research/v8-no-work-100-20260907/experiments/run_post_query_functional.sh \
  leaf docs/research/v8-no-work-100-20260907/experiments/post-query-lean-v4.log
```

The first command exports a previously missing `ImageCallbackInterfaces.olean`.
Its existing source/evidence were already checked; absence of an importable
artifact justified this one focused replay. Do not repeat it unchanged when
the pinned artifact is present. The runner rejects overwriting existing logs.

| Run / log | Exit | Wall seconds | Peak RSS bytes | Swaps | Status |
|---|---:|---:|---:|---:|---|
| `post-query-interface-v1.log` | 0 | 4.05 | 5,673,254,912 | 0 | Missing-cache export; nine standard-axiom audits |
| `post-query-lean-v1.log` | 1 | 8.95 | 5,524,340,736 | 0 | Initial structure binder/proof elaboration errors |
| `post-query-lean-v2.log` | 1 | 3.83 | 5,562,187,776 | 0 | Local reduction-depth failure at concrete folded-vector comparisons |
| `post-query-lean-v3.log` | 1 | 3.85 | 5,569,331,200 | 0 | Symbolic lemmas proved; application still unfolded concrete definitions |
| `post-query-lean-v4.log` | 0 | 4.51 | 5,747,523,584 | 0 | Explicitly unfold only difference/noise, then apply symbolic identities; 16 standard-axiom audits |

The final proof uses no increased recursion allowance, no `sorry`, and no new
axioms. All final audit entries contain only `propext`, `Classical.choice`,
and `Quot.sound`. Failed logs contain Lean's error-recovery placeholders;
they are failure evidence, not retained claimed results.

Final pins:

```
PostQueryFunctional.lean
123f92dbdcd2fb986d12fe2a394d7377d4304bb48714e1319e1dcf07ea8935df
PostQueryFunctional.olean
1e4129d9a643b5812c1a64fb893a4bbccbcc45c7c28a9509ff20878ae6355294
ImageCallbackInterfaces.lean
5d6d1f5be0a0351c1288c975355f944a9ea447d90c8c40d0b57898138ec6cdd8
ImageCallbackInterfaces.olean
33b837a6e80e0697281a0195ea87dc5419852b91653523503e228cd79d2535b5
```

## Decision / unchanged accounting

This is a useful constructor advance: the ordinary/image fold, actual
natural-line query functional, degree-q shifted discrepancy, and compact
three-round tail now connect without placeholder equality premises. It does
not establish anchor coverage, an efficient extractor, authentication-good
probability, full-view simulation, a resource-bounded Fiat–Shamir theorem or
Rust-to-Lean translation. Those terms remain unresolved, not numerically zero.

The proof-body model is unchanged at
`697*16 + 52 + 24 + 22*621 + 2*296*26 = 40,282` bytes. There are no new verifier
operations. This run makes no new CU-parity or proving-time claim. The
[ordered noisy post-query game](ordered-post-query-review.md) is now
instantiated with this constructed functional; its completed conditional
bound retains the actual anchor-to-received support obligation. The next
source/game interface is the causal pre-alpha0 constructor, alongside the
bounded-sampler/Fiat–Shamir connection. Neither continuation can discard the
remaining accepted recovery mass merely because this post-query interface is
complete.
