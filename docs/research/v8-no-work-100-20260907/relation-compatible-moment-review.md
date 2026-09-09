# Relation-compatible far-final acceptance

Research continuation from `edb199c12fcc41f00330298b95b4736f60ac6f3a`.
The focused leaf is Lean-checked. No numerical bound on the remaining moment
is assumed.

## Exact remaining event

Fix the complete prefix immediately before fresh ordered distinct queries.
It includes the actual first compact response and the actual final256 chosen
after alpha0. Let

```
delta = carried - dot(folded ordinary/image weights, actual final256)
M = #{final-domain positions where actual final256 equals the folded received word}.
```

The received word is an arbitrary function. It is not replaced by a polynomial
anchor. For any event E determined by this prefix, the proved new reduction is

```
Pr[actual compact suffix accepts AND E]
 <= E[1_E * 1_(delta=0) * choose(M,q)/choose(T,q)]
    + (q/|G| + 18/|A|) * Pr[E].
```

Here rho is uniform in G, and each of the three later relation challenges is
uniform in A. Ordered queries are uniform embeddings `Fin q -> D`, independent
conditional on the entire prefix. `RawRounds` retains each later response's
dependence on previous challenges. These are ideal conditional laws, not a
claim about Fiat-Shamir prequeries or retries.

For E = wrong early-C1 claim AND far actual final, the first term is the
relation-compatible far agreement moment. Unlike a query-distance-only
screen, it retains the actual carried scalar equation. A nonzero prior cannot
be erased by all-zero query residuals because the query batch is shifted.

The theorem does not establish that the moment is small. In particular,
alpha-adaptive final choice is not a degree-six polynomial in alpha. Correcting
one final direction with nonzero folded weight can force delta to zero, at a
potential cost to agreement. The separately developed `AdaptiveFinalPrior`
control addresses this distinction; it is not an acceptance probability or
payment forgery.

## Existing results consumed, not enlarged

| Result | Valid reuse | Remaining condition |
| --- | --- | --- |
| `PostQueryFunctional.post_discrepancy` and `tail` | Literal plus-update functional yields `prior - rho*sum residual_i*rho^i`; actual compact terminal corresponds to terminal zero | Field/source-shaped model, not translated Rust/parser/authentication |
| `OrderedQueryGame.ordered_matching_ratio` | Exact ordered schedule mass `choose(M,q)/choose(T,q)` | Fresh ideal ordered schedule; no permutation-invariant tail assumption |
| `JointImageGame.shifted_nonzero`, `shifted_degree` | Generic numerator q, including a nonzero prior | Queries and prior fixed before rho |
| `JointImageGame.rounds_false_bound` | Three remaining degree-six repairs, numerator 18 | Causal raw compact grammar |
| `HelperJointGame.early_c1_wrong_claim_bound` | Wrong claims against the earlier C1 message, within the supported close-final region | Does not cover the far-final moment |
| `FixedC1HelperReduction` | Three unknown helper lanes give degree two on the fixed C1 own-support | Excluded C1 fibres remain arbitrary; normalized false-C1 claim contains `gamma^-26 * c1Error(gamma)` |
| `ThreeHelperClaimCover` and `GenericOODClaimGame` | Constructed pre-gamma full tuple permits a degree-28 claim-error root bound | Existing cover applies only to close image-valid reconstructed candidates |

The helper degree two is therefore not a substitute numerator for a false-C1
claim. Its false low-lane polynomial has degree at most 25; after the helper
contribution is restored, the original unnormalized full claim can have degree
28. Nor does a tuple chosen before gamma automatically precede earlier
semantic/copy challenges.

## Composition and overlap

The new suffix reduction charges only rho and the three **later** relation
repairs. It does not charge the first relation response's six roots, image
mixing, shifted kappa rows, or gamma claim errors. It accepts an arbitrary
incoming carried claim and allows the actual final to depend on alpha0.

Adding its far-region bound to the existing coarse near-region ceiling is a
valid union bound, but repeats rho/later budgets across disjoint prefix events.
To charge them once, retain event masses as above or first partition the common
suffix bad event and separately prove the near/far compatible-moment bounds.
The old coarse theorem alone does not justify subtracting its repair terms or
taking a maximum. No historical `396430` inventory is imported.

## Evidence and execution

The new leaf is
[`RelationCompatibleMoment.lean`](experiments/RelationCompatibleMoment.lean);
its guarded runner is
[`run_relation_compatible_moment.sh`](experiments/run_relation_compatible_moment.sh).
The runner pins borrowed formal sources to `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`,
checks the existing causal-game olean against its recorded green artifact,
records the entire imported source/olean closure before and after, and caps the
single focused job at `-M7000` plus an independent 7 GiB aggregate RSS guard.

Reproduction from the research worktree:

```sh
bash docs/research/v8-no-work-100-20260907/experiments/run_relation_compatible_moment.sh \
  /absolute/path/to/a-new-moment-log.log
```

| Focused run | Exit | Wall time | Peak RSS (bytes) | Swaps | Result |
| --- | ---: | ---: | ---: | ---: | --- |
| [v1](experiments/relation-compatible-moment-v1.log) | 1 | 37.76 s | 5,220,663,296 | 0 | Core three endpoints checked; causal wrapper had a local addition orientation mismatch |
| [v2](experiments/relation-compatible-moment-v2.log) | 0 | 39.91 s | 5,265,129,472 | 0 | One-line orientation fix; all four endpoints checked, imported provenance unchanged |

`schedule_false_bound`, `suffix_bound`, `supported_bound` and
`causal_supported_bound` each audit to only `propext`, `Classical.choice`, and
`Quot.sound`. The failed log is retained, not used as a release certificate.
The source SHA256 is
`46bcc1742e832f54dd075da6b13a69c859d46daf3951ab6928f8b4dc6b52c726`;
the green olean SHA256 is
`b1dd5289ad8aeb2fcaca16251b66c4c64922117afd23ce4f74e2c91cb111c8a6`.
Lean was 4.32.0, commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`;
mathlib was `81a5d257c8e410db227a6665ed08f64fea08e997`.
The concurrent main/cache revision recorded in both runs was
`db7a1847b4197a03e7772ca68132ce8fb2d861bf`, while imported formal sources were
checked against their older explicit pin, not assumed to match that HEAD.

This is a proof-layer change only: no messages, parser changes, verifier
operations, Rust execution, SBF build, proving benchmark or CU result. The body
model remains `697*16 + 52 + 24 + 22*621 + 2*296*26 = 40,282` bytes. Full-view ZK,
authentication/source correspondence and resource-bounded FS remain separate.

The earlier polynomial-raw `ChordRationalQueryGame` draft and runner were
paused before any preflight/build when the task priority changed. They are not
retained checked endpoints or dependencies of this result.

## Decision and next experiment

The far-final task is now a precise scalar-constrained agreement problem,
consuming the actual causal compact suffix. This is a stricter obligation than
query distance alone, not an achieved small probability: the symbolic moment
is still the missing term. The next decisive test should maximize
`1_(actual prior=0) * choose(M,q)/choose(T,q)` over legal post-alpha finals in
the fixed-C1/helper-degree-two reduced game, retaining wrong-C1 component
claims and the pre-alpha first response. It must preserve the degree-28 full
claim error and report strategy scope. A large attainable moment would reject
an overstrong relation-tail lemma without proving a payment forgery.
