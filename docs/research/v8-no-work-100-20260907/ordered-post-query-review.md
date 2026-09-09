# Constructed ordered post-query game and selected pair decoding

Continuation from `5e26df14ad5fc674d5ea43d02431f1dc9ef682fa` on
`research/v8-no-work-100-20260907`. Research only; no verifier, production,
transcript, proof-body or runtime changes. The concurrent main worktree is
read-only and its unrelated K1 proofs are neither imported nor committed.

## Result

The post-query game now consumes a constructed natural-line functional and
actual compact response strategy. Its caller no longer supplies the crucial
`same_prior`, `zero_iff`, final-degree or terminal-correspondence equalities.
The ordered query array, including its effect on rho powers and later
responses, is retained in both the functional and the probability game.

A second checked bridge derives input-pair validation and all 24 direction
bit parses from a concrete subset of selected C1 residuals. It connects the
decoder's actual row914 digest to the separate row1017 occupancy certificate;
it does not assume they are equal or that decoding succeeds.

The early-C1 concrete agreement-cap interface is also checked. Specializing
the optional-object theorem remains open: the isolated application hit the
memory guard, not a mathematical counterexample. The source and failure
evidence are in [its report](early-c1-identification-notes.md). None of these
results makes a mathematical tuple into a resource-bounded payment extractor
or supplies a global 100-bit theorem.

## Why query order needed a real interface repair

The source sampler retains first-occurrence order. The query functional uses
`rho^(j+1)` at ordinal `j`; the transcript and later responses may also depend
on that order. Independently sorting Merkle entries does not sort this array.
The previous `JointImageGame`/`RobustImageGame` continuation was indexed by an
unordered query `Finset`. That interface cannot represent every actual
order-dependent continuation simply by choosing one sorted representative.

The new [OrderedQueryGame](experiments/OrderedQueryGame.lean) uses embeddings
`Fin q ↪ D`. It counts ordered matching schedules and proves that their
probability is still `choose(M,q)/choose(T,q)`: the common `q!` cancels. It
does **not** assume permutation-invariant scalar acceptance, charge a `q!`
union loss, or change the verifier's sampler.

The small regression in [audit_ordered_queries.py](experiments/audit_ordered_queries.py)
shows why order matters: over F7, with rho=3 and prior=0, residuals `(1,2)`
give shifted discrepancy zero, but `(2,1)` gives 6. This is not a complete
proof or attack. The [recorded checks](ordered-query-checks.json) also exhaust
1,008 small matching profiles and 50 bounded first-occurrence profiles
(16,949 tapes counting each profile). They validate reduced combinatorics,
not QM31 security or all causal strategies.

There is already reusable ideal bounded-sampler mathematics:
`V5BoundedQuerySamplerUniformity.conditionedScheduleProbability_eq_uniform`
proves uniform ordered schedules conditional on success of an IID finite
draw tape; `unconditionedSuccessfulBadProbability_le_ideal` counts aborts as
rejection. Reusing that generic lemma is legitimate; importing the older
work-normalised numerical ledger is not. The actual V8 call is q22 over
2^18 positions with a cap of 64 **word draws**, not 64 eight-word blocks.
Rust/SHA block consumption, transcript post-state, leftover-word information,
conditional freshness of rho and the nonce/retry/oracle-query FS lift remain
separate obligations. No new sampler replay was needed here.

## Constructed functional and conditional theorem

Let Q be a reference quotient, fixed as an analysis object in the prefix,
and let Q* be its first primal fold. The received folded word R remains an
arbitrary function. The actual final F may have been selected after alpha0,
but is fixed before fresh queries. Suppose, explicitly, that

```
R(x) = Eval(Q*,x) for x in D outside B.
```

This is a support hypothesis, **not** an acceptance consequence proved by
this continuation. The new constructor does not silently declare R to be a
global polynomial or identify the quotient with its image reconstruction.

With W* the image-aware dual-folded functional and c* the actual compact
first-response evaluation, [PostQueryFunctional](post-query-functional.md)
constructs both source additions:

```
W_rho = W* + sum_j rho^(j+1) * evaluation_weight(x_j)
c_rho = c* + sum_j rho^(j+1) * R(x_j).
```

It derives the discrepancy
`prior - rho * sum_j residual[j]*rho^j`, where
`residual[j] = Eval(F,x_j)-R(x_j)`. The general degree is q. A correct prior
is not assumed to obtain a q-1 numerator.

[OrderedPostQueryGame](experiments/OrderedPostQueryGame.lean) then constructs
the ordered probability game from this functional and the actual three
compact raw tail rounds. The tail strategy may depend on the full ordered
schedule and rho, and each subsequent response may depend on earlier alpha
challenges. Its two endpoints are:

| Endpoint | Additional prefix condition | Conditional tail-acceptance bound |
|---|---|---|
| `wrong_reference_bound` | The actual first-response discrepancy against Q* is nonzero | `choose(|B|+255,q)/choose(T,q) + q/|G| + 18/|A|` |
| `different_final_bound` | F differs from Q*; no wrong-reference premise | Same bound |

Here queries are uniformly distributed ordered distinct schedules, rho is
fresh uniform in the nonempty challenge set G, and each later alpha is fresh
uniform in nonempty A. For the intended ideal law, `|G|=k-1`, `|A|=k`.
The bounds are uniform in the fixed prefix. One can classify wrong reference
first, then different final if the reference discrepancy is zero; these
disjoint prefix cases have the same bound without a factor two. This is not
permission to condition on acceptance or on a later successful replay.

For B=9301, q22, T=262144 the exact restricted bound is

```
epsilon_post = choose(9556,22)/choose(262144,22) + 22/(k-1) + 18/k.
```

The exact rationals, current-source hashes and final axiom audits are in
[ordered-post-query-evidence.json](ordered-post-query-evidence.json), generated
by [the audit](experiments/audit_ordered_post_query.py). This is a conditional
post-query bound, not an additional independent global error allowance.
The earlier near ceiling exceeds it by `31/(k-1)+6/k`: its 28-degree gamma,
3-degree shifted-row and first 6-degree relation stages. In that image-valid
near branch there is no extra image-root term. This subtraction explains
overlap; it is not a proof that the entire source instantiates those stages.

## Exact interface and dependency status

| Boundary | Checked here / reused | Still required |
|---|---|---|
| Four circle slots to final polynomial | Natural-circle four-slot identities, normalized fold, line degree <=255; exact V7 stored-domain injectivity | Component/chord quotient openings instantiate the polynomial class; arbitrary received values are not assumed polynomial |
| `same_prior` | Difference-polynomial zero implies final coefficient equality; actual compact discrepancy is then preserved | A reference Q with the required image/support properties |
| Query `zero_iff` and shifted discrepancy | Literal natural-line evaluations, ordinal rho powers and signs | Byte parser, canonical fields, authenticated values and optimized Rust arithmetic refinement |
| Tail acceptance | Raw six-field compact responses construct causal three-round repairs; acceptance iff terminal-zero | The preceding first response must be constructed before alpha0, not inferred from a post-alpha0 snapshot |
| Ordered ideal queries | Embedding count and uniform local game bound | Bounded sampler/post-state/source coupling and resource-bounded FS |
| C1 to input-pair decode | Two exact right-child copy edges, occupancy equations, selected-side copy and 24 Boolean directions | Acceptance implies those individual residuals; full path hashes, owner/note/nullifier/public context and settlement |

Reused V7-consumed files include `V7ExactOneFoldDomains`,
`V7PairLeafOccupancy`, `V5FriConcreteEncoderApplicability`,
`V5FriInitialCircleEncoderIdentity`, `V5FriConcreteEncoderCommutation`,
`V6RelationFold` and `V6TranscriptRelationGrammar`. V5/V6 names identify
deterministic dependencies already used by V7, not adoption of V5's security
ledger. The selected optimized functional binds a compact 545-byte public
description, **not** the obsolete dense 16,384-byte weight hash. No hashing
or arithmetic change is made by these proofs.

The [input-pair report](selected-pair-decoder-review.md) gives exact cells and
the validator's field-stage correspondence. Its successful returned pair is
constructed from residuals, not an assumed `Valid` input. Direction parsing
does not establish hash membership; the old amount proof's strict positivity
gap is not solved by occupancy. Full-view masking is not inferred from these
deterministic footprints.

## Total accepted-extraction accounting remains explicit

Let A denote acceptance by the intended complete repaired verifier; X means
the specified bounded extractor returns a witness passing the independent
payment/context/transition checker. The following is a bookkeeping template
for A AND NOT X, not a completed source partition theorem. Each row excludes
earlier rows. Successfully extracted out-of-radius executions are outside
this failure event from the start.

| Precedence | Failure class | Present evidence / missing implication |
|---|---|---|
| 1 | Access/replay/authenticated graph/canonicality/fuel/provenance/challenge mismatch | Must construct the actual bounded extractor and source/ideal coupling; `none` and aborts remain visible |
| 2 | Coupled near-regime small-Good or false component-point binding | Existing restricted near theorem; does not bound all near executions |
| 3 | Remaining supported-prefix wrong reference or different final | New constructed ordered tail bound; its query/rho/repair terms overlap row2's all-stage theorem |
| 4 | C1 recovery failure | Separate qualifying close tuple/private sampling from uncovered/far failure; generic common-sample Gao result is conditional on exact access/encoder/private coins |
| 5 | Recovered coefficients but selected individual semantic/copy/public constraints fail | Correct gamma point claims alone do not prove these earlier constraints; preserve C1-before-lambda/chi boundary |
| 6 | Constraints hold but decoding, witness validation/context/settlement or bounded resources fail | Amount and new input-pair/direction slices only; remaining deterministic endpoint open |

Replay outcomes and decoder failures can depend on later observations. Their
absence is **not** a pre-query conditioning event. To upper-bound a row, it
must be dominated by a justified event in the coupled ideal game, conditioning
only on its actual causal prefix. Neither source correspondence nor an absent
extractor is assigned a tiny probability. Global unsupported terms stay
symbolic/null; the old 396430 inventory is not imported.

Original/paired root products remain far/uncovered cases. The high-J example
retains own-support recovery, not same-support recovery. T512 uses the earlier
restricted invalid-image game; the zero-fold image kernel still forbids a
late final-only image check. Shifted-row, late-inactive, shifted-query/later
repair and radius-boundary regressions retain their prior scopes. No unchanged
regression was replayed and none is removed by this partition.

## Execution and unchanged cost

All new proof jobs were serialized focused leaves using pinned Lean4.32.0
and Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`. Imported Aspis sources
were matched against the research revision and the read-only cache worktree;
the ordered bridge logs its transitive source/olean closure before and after.
Missing local exports of `RobustImageGame`, `ImageCallbackInterfaces` and
`V7PairLeafOccupancy` were built once, not a package replay.

| Final target | Exit | Wall seconds | Peak RSS bytes | Swaps |
|---|---:|---:|---:|---:|
| `PostQueryFunctional` | 0 | 4.51 | 5,747,523,584 | 0 |
| `OrderedQueryGame` | 0 | 7.12 | 5,675,220,992 | 0 |
| `OrderedPostQueryGame` | 0 | 3.36 | 5,642,469,376 | 0 |
| `SelectedPairDecoder` | 0 | 3.25 | 5,648,973,824 | 0 |
| `EarlyC1Identification` (three agreement-cap declarations only) | 0 | 3.27 | 5,657,886,720 | 0 |

Each retained audit uses only `propext`, `Classical.choice`, `Quot.sound`.
Failed local elaboration/reduction runs remain in their named logs; their
error-recovery `sorryAx` output is not successful theorem evidence. Concrete
reduction failures were replaced by symbolic identities and explicit unfolding
of only the required definition, without increasing recursion or memory caps.
The early-C1 report records its additional guarded failures and final scope.

PostQueryFunctional used `-M7000` with a live Lake parent; the newer ordered,
payment and C1 runners resolve the Lake environment first and independently
stop aggregate descendants at 7 GiB. The older runner must not be described
as having that extra guard. The ordered runner's retained post-run hardening
adds fail-closed source/olean checks for already logged local imports; it does
not change a checked Lean source or justify an unchanged replay.

Reproduction (fresh log paths; use the pinned caches, do not rebuild a cold
dependency graph):

```sh
bash docs/research/v8-no-work-100-20260907/experiments/run_ordered_query_game.sh leaf /absolute/NEW-ordered.log
bash docs/research/v8-no-work-100-20260907/experiments/run_ordered_query_game.sh bridge /absolute/NEW-bridge.log
python3 docs/research/v8-no-work-100-20260907/experiments/audit_ordered_post_query.py --check-recorded
```

The other two leaf commands and cache pins are in their linked reports.
The machine audit verifies the final current-source logs, not the existence
of a file named `.olean` alone. No new Rust, SBF, full-prover, extraction-time
or CU benchmark was run. The body remains exactly
`697*16 + 52 + 24 + 22*621 + 2*296*26 = 40,282` bytes. Prior maximum-body
measurements remain 1,015,793 / 1,028,546 / 1,034,027 / 1,047,041 complete CU
for the four shapes; they are not universal bounds over accepted inputs.

## Decision

QM31 q22 remains the primary research profile. This continuation removes
post-query correspondence premises and advances a real payment decoder slice,
without extra bytes, challenges or verifier operations. It does not close
accepted uncovered recovery, executable extraction, the full payment endpoint,
the resource-bounded Fiat–Shamir theorem or adaptive full-view ZK.

The next decisive interface experiment is a **causal pre-alpha0 constructor**:
freeze the actual ordinary scalar/weights and quotient prefix, derive tau,
take response0 before alpha0, and instantiate the constructed ordered tail.
Prove the first discrepancy distribution from that strategy, then connect
the existing row/near game. A post-alpha0 snapshot cannot discharge it. This
is a bounded source-shaped task; the global far-recovery obligation remains
separate and must not disappear when that interface succeeds.
