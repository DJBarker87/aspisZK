# Insufficient own support: charge the common-query branch

Continuation of `ed41b2537e7dad15ce8055d9e5524e337ee8b9a4`. This is a
focused mathematical event count, with no Rust, verifier, transcript or
production changes. The fixed-tuple, adaptive-family and selected-source
leaves are kernel-checked, including the actual declared ≤111 tuple family.

## The specific improvement

Fix the received component words, one component tuple, its residual
polynomials, chord denominators and exception set before gamma. Let C be
the complete fibres where all component residual polynomials are zero.
Let G and A be explicit gamma/alpha sets, and choose q distinct query fibres
uniformly from the original domain U. The supported event may constrain an
actual final selected after alpha; the theorem does not freeze that final.

The new input is not another query averaging identity: **if the supported
event occurs on an all-common query schedule, gamma must lie in a fixed
exception set E**. The parallel symbol residual theorem supplies this
information when the original batch has at least 38,230 matching symbols
but the tuple itself has fewer than 38,228 jointly matching symbols.
At least one matched symbol then lies outside the tuple's own support.
Its nonzero, fixed, degree-at-most-28 gamma residual vanishes.

An insufficient tuple's common complete fibres satisfy J=|C|≤9,556 because
each complete fibre supplies four distinct jointly matching symbols.
The parallel `OwnFibreGeometry` leaf supplies the symbolic four-to-one
relation; `common_fibre_cap` consumes it without enumerating the large
domain. Its selected received-word instantiation is in `SelectedOwnSymbol`.

For every fixed tuple the proved exact integer upper-bound numerator is

```
choose(J,q) * |E| * |A|
  + (choose(T,q)-choose(J,q)) * (d*|A|+(|G|-d)*3),
```

where T=|U| and d=28 for the component batch. After division by the original
`choose(T,q)*|G|*|A|`, this is

```
beta(J) * |E|/|G|
  + (1-beta(J)) * [d/|G| + (1-d/|G|)*3/|A|].
```

The first term is **not** beta(J) alone. The second term reuses the existing
`pointwise_bad_schedule_count` and `wrong_support_count`: choose one bad
fibre/slot from the fixed schedule before gamma/alpha, then apply the two
root bounds. No union over fibre locations or query indices is introduced.

## Poles and actual scheduling

The existing integrated fixed-target theorem required every denominator
in U to be nonzero. The new wrapper does not assume that property.
For each schedule separately:

1. If any queried slot has a zero denominator, the supported actual event
   must be false, by its explicit source rejection premise.
2. Otherwise, the selected bad slot is non-polar and the existing joint
   gamma/alpha bound applies.

The query domain and normalizing denominator are unchanged. We do not
resample over a non-pole domain or silently condition its law. Totalized
field division by zero is not a substitute for actual rejection.

The retained count is over q-subsets. A genuinely fresh ordered distinct
query law yields the same geometric ratio using the existing
`OrderedQueryGame.ordered_matching_ratio`; order-sensitive rho and later
responses remain outside this pointwise event. These leaves do not claim a
new transcript sampler law or a complete ordered-source refinement. The
generic fold core proves the negative sign in `final - folded_virtual`;
the separate selected adapter targets exact zero-check equivalence, which
is the interface used here. No concrete full residual-value identity is
needed or claimed by the selected count. The source capture implication
must hold for the actual same Q, image reconstruction and represented final.

## Fixed family and adaptive selection

`InsufficientOwnSupportFamily` accepts a finite family fixed before gamma
and an arbitrary actual event captured by at least one member's supported
event. It does not require choosing that member before alpha. Its exact
bound is the sum of the above **charged** expressions, preserving each
member's own J and |E|. With family size≤111, J≤9,556 and |E|≤e, the coarse
normalized expression becomes

```
111 * [beta(9556)*e/|G| + d/|G| + (1-d/|G|)*3/|A|].
```

There is no `111*beta(9556)` term. The family multiplier applies to joint
algebraic collision terms, including the gamma charge on common schedules.
Membership, the coverage implication, exception construction and fixed
timing are explicit prerequisites; this is not a bound for an arbitrary
post-challenge target or every accepting execution.

`SelectedOwnSupportGame` removes those interface placeholders
for a precisely defined selected event. Its candidate Q can depend on
gamma and alpha; it must belong to the literal received-word quotient
family, satisfy the carried image constraints, reconstruct the selected
gamma batch of the same tuple, and have legal queried denominators and
literal equality between the final evaluation and received fold. The
selected query adapter relates this equality to the actual zero residual
check, preserving its acceptance predicate. The final is Q's
actual coefficient fold; `of_actual_final` captures this represented-final
branch from an independently supplied final and equality proof. It does
not assert that every final is represented.

The selected proof obtains exact cubic zero-check equivalence from
`TupleQueryTransport`, the common set and gamma exception from
`SelectedOwnSymbol`, and then applies the family count. The exception cap
used for the coarse statement is safely `28*1048576 = 29360128`: an upper
bound on own-support size cannot be substituted as a lower bound when
bounding its complement. The endpoint `literal_family_count` uses the
actual `LinearMessageFamily.family (SelectedFactorCoherence.parent c1 c2)`
and derives its cardinality bound from the fixed nonzero parent and its
Y-degree. The family is pre-OOD/pre-gamma, not necessarily pre-lambda.
Its focused v5 check is green. This is the literal represented pointwise
event, not a claimed coupling to every complete verifier execution.

Scalar acceptance with failed pointwise checks remains in the one existing
shifted-rho/later-repair error event. This proof does not introduce another
copy of that charge. Higher-Y factor cases, missing source/authentication
interfaces, early-C1 projection, efficient extraction, semantic/context and
checked-payment validation remain separate until the corresponding source
composition is proved.

## Exact prerequisite falsification

`experiments/insufficient_own_support_control.py` exhausts 126 outcomes per
tuple in one predeclared F7 residual family: three query fibres, q=1, six
nonzero gammas and all seven alphas. It uses the literal four-slot fold at
x=y=1. Two fibres are identically correct; the third has residual gamma−1
in all four slots. E={1} is fixed, not selected from the actual gamma.

| Diagnostic | Exact count | Consequence |
|---|---:|---|
| Gamma-charged event | 21 | Below joint bound 36 |
| Its all-common schedules | 14 | Exactly 2 common schedules ×1 exception ×7 alphas |
| Remove the gamma charge | 91 | Exceeds 36; the new event premise is necessary |
| Choose singleton E={actual gamma} retrospectively | 84 common outcomes | Cardinality alone does not establish prefix fixing |
| Allow a queried zero denominator through totalized division | 42 wrong-schedule outcomes | Exceeds the bound 22; actual rejection must remain |
| Retain pole rejection and fixed E | 14 | Query domain was not renormalized |
| Adaptive selection from two predeclared tuple events | 42 | Covered by their charged union bound 72 |

This is exhaustive over the displayed small residual family and outcomes,
not over all causal strategies or the real verifier. It is not a payment
trace, a forgery, or experimental evidence of QM31 probabilities. The
retained JSON is `experiments/insufficient-own-support-control.json`.
The script ran with exit 0; wall time was below 0.01 s. No large field or
polynomial enumeration was performed.

Exact command from the research worktree:

```sh
python3 docs/research/v8-no-work-100-20260907/experiments/insufficient_own_support_control.py
```

Script SHA-256: `8ed4fe493d1c1897cceb0fcfc24a71b21f9756bff9d72e3f386512ef20fc417e`.
This trivial preflight did not record peak RSS and is not a substantive
arithmetic benchmark or release measurement.

## Proof/evidence map

- `InsufficientOwnSupport.lean`: seven audit endpoints, including the
  source-event guarded bad-schedule count, charged fixed-tuple numerator
  and exact normalization. Green v2.
- `InsufficientOwnSupportFamily.lean`: four audit endpoints for adaptive
  capture, exact family sum, coarse size bound and normalization. Green v2.
- `SelectedOwnSupportGame.lean`: seven audit endpoints deriving the literal
  pointwise/pole/exception inputs and instantiating the actual ≤111 family.
  Green v5; `literal_family_count` is the final selected count endpoint.
- Frozen `FixedTargetQuerySupport.lean` source SHA-256:
  `61e265e65c15bcee5f21d3aea671a734bf55657d9ca736866348396ac2b25dad`.
  Its missing compatible compiled artifact was exported separately;
  no copy of its already completed theorem is re-proved in these new files.

NUC scope: `/home/dombarker/project-offloads/aspis-own-support.f6NQzi`,
runner `run_own_support_nuc.sh`, parent pin above, borrowed-source pin
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`. Every focused check requires
the parent's serialized build grant and retains its exact source snapshot,
command, manifest, exit, wall/RSS/swap and axiom audit. Native package
cache provenance does not mean those packages were freshly replayed.

| Attempt | Exit | Wall | Peak RSS (KiB) | Swaps | Scope |
|---|---:|---:|---:|---:|---|
| InsufficientOwnSupport v1 | 1 | 3.09 s | 6,655,720 | 0 | Nat-cast sum glue and redundant final tactic |
| InsufficientOwnSupport v2 | 0 | 3.41 s | 6,688,456 | 0 | seven standard-only axiom audits |
| InsufficientOwnSupportFamily v1 | 1 | 3.02 s | 6,653,484 | 0 | missing parentheses around two-term sum bodies |
| InsufficientOwnSupportFamily v2 | 0 | 3.21 s | 6,685,012 | 0 | four standard-only axiom audits |
| SelectedOwnSupportGame v1 | 1 | 3.27 s | 6,827,548 | 0 | overly broad equality-decision override changed Checked's instance |
| SelectedOwnSupportGame v2 | 1 | 3.00 s | 6,825,316 | 0 | auto-unfolding of large symbolic exception sets |
| SelectedOwnSupportGame v3 | 1 | 3.08 s | 6,828,176 | 0 | final simplification unfolded the count |
| SelectedOwnSupportGame v4 | 1 | 3.07 s | 6,828,352 | 0 | actual Fin instance differed from standard cardinality lemma |
| SelectedOwnSupportGame v5 | 0 | 3.14 s | 6,862,244 | 0 | seven standard-only axiom audits |

The replacement adds only `Nat.cast_id` to one common-schedule sum and
removes a `ring` after the normalization goal was already solved. No limits
were increased. Exact failed/green source snapshots, logs and per-run
manifests are retained as `insufficient-own-support-nuc-v{1,2}.*`.
The failed diagnostic's `sorryAx` is not a retained proof claim.
Green source: `de451549502893a787f07677df5256129f47c27ceb7501af9a6343daa29d6915`.
Green output: `dfe353715f05bea229c969e1b4e89cf4dc3869cca69c2db763bfbc8922d515a6`.

The family v1 parser placed a second addend outside its finite-sum binder;
v2 adds explicit parentheses, and removes an unreachable final `ring`.
It does not change the intended summand or theorem hypotheses. All attempt
triplets are retained as `insufficient-own-support-family-nuc-v{1,2}.*`.
Family green source: `0d7f6728c0f602baca7237986bc461431b101f8f4c81e3ba5a622f5ac1868ce7`.
Family green output: `d05bbf321aa6318498bcadc4090f8f475020f3f775f81f8e3a758edc839dbcb3`.

The selected fixes retain the ordinary `Data.Checked` equality-decision
instance, make the named common/exception sets and total count locally
opaque during elaboration, and use `Fintype.card_congr` to transport the
actual source instance's cardinality to the standard Fin instance. They
do not alter the event, remove any premise, increase a limit, unfold a
large enumeration or edit an imported green source. Failed versions are
diagnostics only; their `sorryAx` output is not retained as a proof claim.
Every attempt's source snapshot/log/manifest is retained under
`selected-own-support-game-nuc-v{1,2,3,4,5}.*`.
Selected green source: `d88191286d55e16a46e424517a01c4ad9a081f5d0c5722c5764c43d4dcb64c1d`.
Selected green output: `89ce3ef20dcf88fff75cf78947d2c2d966c1f189914746901ef0440ffec1fcd6`.
Final per-run manifest: `b6c80a29f7b2e314fc83502cfb548535ad1977db8b3e53eefb7066fd4e9132ba`.

The final recorded invocations used the shared runner as follows (these
are evidence commands, not instructions to replay unchanged green leaves):

```sh
bash /home/dombarker/project-offloads/aspis-own-support.f6NQzi/run_own_support_nuc.sh \
  /home/dombarker/project-offloads/aspis-own-support.f6NQzi \
  InsufficientOwnSupport insufficient-own-support-nuc-v2
bash /home/dombarker/project-offloads/aspis-own-support.f6NQzi/run_own_support_nuc.sh \
  /home/dombarker/project-offloads/aspis-own-support.f6NQzi \
  InsufficientOwnSupportFamily insufficient-own-support-family-nuc-v2
bash /home/dombarker/project-offloads/aspis-own-support.f6NQzi/run_own_support_nuc.sh \
  /home/dombarker/project-offloads/aspis-own-support.f6NQzi \
  SelectedOwnSupportGame selected-own-support-game-nuc-v5
```

No global budget term is booked from these conditional statements.
The body remains 40,282 bytes; new messages/verifier operations are zero.
No proving, SBF, complete-transaction CU or extractor runtime was measured.
Full-view privacy and resource-bounded Fiat–Shamir remain independent;
grinding supplies zero security credit.
