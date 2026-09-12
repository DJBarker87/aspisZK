# What the 97.19-bit screen does, and does not, say

Read-only source audit, 2026-09-12, base `ab4f61feaca096ae3dae66e39d29f6e36bdca0ec`.
No Lean/Rust build, cache mutation, new probability claim, or proof-source edit.
Paths under `../v8-no-work-100-20260907/experiments/` below are the retained
Lean sources; their historical checked status is not a new replay result.

## Exact event and arithmetic record

`EarlyC1Projection.earlyC1` is `EarlyC1Projection.early fibreEncode
(receivedFibres c1) 245609`. It is a noncomputable optional tuple of 26
codewords with at least **245609 complete own-support fibres out of 262144**.
It is not the existence of a C1 commitment, answer prefix, fixed extracted
word, or minority-family member.

`SelectedHigherYNoEarlySupport.no_early_support_cover` proves, from
`e.data.Checked` and `earlyC1 e.c1 = none`:

* `NearGammaSelectedC1.good e.c1 e.c2 Gamma` has cardinality at most 63;
* every actual image-valid `Q : Fin 1024 → K`, outside that fixed Good set,
  has `fibreCount (e.raw gamma) Q ≤ 252847`.

Its `outside_good_support_cap` does not even require `earlyC1 = none`.
These statements neither remove the middle band `200808..252847` nor assert
probability, authentication, or successful witness extraction. `none` is a
legitimate analysis predicate on a fixed C1 word, but no inspected selected
Rust verifier check computes or branches on this noncomputable selector.

The exact **97.1879093395618-bit** record is
[`higher-y-fixed-c1-screen.json`](../v8-no-work-100-20260907/higher-y-fixed-c1-screen.json),
`terms.no_early_naive_extended_layer_cake`. It extends the existing support
layer cake from `9558..200807` to `9558..252847`, at q22. The JSON explicitly
labels this `rejected_as_q22_completion`, `passes_100: false`, and the whole
file `exact_arithmetic_screen_not_global_probability_theorem`.

Its stored rational is exactly N/D:

```text
N = 15508311658482797023714925943928884055656821753546089161719558018369575019202916233849019732082257660110566135037754361805796179642099690414852279449259954764351803563981276231121
D = 2799242009514433187830330090877040975254906268552049830344665483037381182894983393265886898896913856230632301959119883400315531671717419461521064640124758896761121465621587707572288362398084298786432090112000
```

The separate stored query-weighted numerator is

```text
16886532595337937123059554326344881186355821190258227284731902271542185748065474614136608019175248373865603
```

The screen uses `|K| = 21267647892944572736998860269687930881`,
`|Gamma| = |K| - 1`, and incidence budget `239599331`. There is no retained
Lean theorem asserting that selected source acceptance has 97.19-bit
soundness. It is the rejected old *bound*, not the `none` predicate itself,
that the newer recovery argument bypasses.

## Authentication does not supply proximity

`AuthenticatedEarlyC1Prefix.prefixWords` and `.fixedC1` are total functions
of recorded answers and the root. `.fixedEarlyC1` separately applies the
near-codeword selector to that fixed word. The strongest relevant existing
authentication theorem is
`AuthenticatedEarlyC1Prefix.accepted_opening_prefix_or_late_target_or_collision`:
an actual accepted path, with advertised-answer consistency, prefix inclusion,
and hash-call coverage, gives the disclosed prefix-word projection or an
explicit late-target/collision alternative.

The same-body consumer
`SameBodyOpenedRun.run_authenticated_opened_or_failure` lifts this to the
actual 22 parsed records and their folded openings against the fixed
`prefixBatch`, not the post-query `observedWord`. Its explicit prefix/root,
answer, and call-coverage premises still matter. Supplying them does not
add a global own-support premise.

There is a direct algebraic obstruction to an authentication-only repair.
Alter one lane of a codeword tuple on exactly 16536 complete fibres and
commit to that resulting total word. The original tuple has support 245608;
any distinct tuple has support at most `16536 + 256 = 16792`, using
`EarlyC1Projection.exact_fibre_overlap`. Thus no tuple reaches 245609.
Authentication can faithfully open a modified committed word. Nothing in
this support calculation requires a hash collision or a late target.
This is a classifier/authentication obstruction, **not** a constructed
full accepted selected transcript or a payment forgery; the historical
[`higher-y-residual-status.md`](../v8-no-work-100-20260907/higher-y-residual-status.md)
also labels its stronger transcript example symbolic rather than executed.

The smallest valid identification implication already exists:

```text
EarlyC1LateProjection.late_projection_identifies:
  ownSupport(c1,c2,p) ≥ 245609
  → earlyC1 c1 = some (c1Projection p)
```

Its converse obstruction is `.none_excludes_qualifying_tuple`; the generic
criterion is `EarlyC1Projection.early_none_iff`. Merkle success or 22 openings
do not produce the displayed own-support hypothesis. Adding another thin
copy of these lemmas would not close a missing interface, so this audit
adds no redundant or false Lean declaration.

## Strongest non-circular route already available

`SelectedMiddleImageRecovery.Recovered` supplies a member of the fixed
at-most-one family, **own original-symbol support at least 38228**, the
actual same-Q gamma batch identity, and C1 projection membership in
`EarlyC1Family`. That minority-family membership is not `earlyC1 = some`:
the predicates and support units differ.

`SelectedResidualHighRecovery.RecoveredHigh` retains the same actual high
witness. Its `.high_residual_probability_bound` bounds high-but-not-recovered
mass by `104 / Gamma.card` under the actual fixed classifier and outside the
same pair-root obstruction. `SelectedResidualRecoveryBound.residual_partition`
is the exact high-unrecovered plus LOW partition with one unchanged compact
suffix. Its `.conditional_nonpair_bound` then proves

```text
residualProbability e (RecoveredHigh e family) A G Gamma
  ≤ 117153/Gamma.card + integratedBudget q Gamma A
      + q/G.card + 18/A.card.
```

It has no `earlyC1 = some` premise. The fixed family/E/beta/sparse/classifier,
checked circle data, nonempty domains, domain cardinal conditions, and
outside-the-product pair-root premise remain explicit. The pair-root product
is the middle obstruction times the singular-row obstruction (degree bound
90407376); one must use that same product and the justified source sampling
law, not a new independently chosen root set. No unconditional security
number follows just from the displayed theorem.

The actionable missing theorem is therefore about the specified extractor:

```text
successful same-body source run
  ∧ RecoveredHigh e family at its actual continuation
  ∧ no already-accounted authentication/semantic/source failure
  → permitted-access extractor returns a witness whose actual
      checked payment validator succeeds for this statement.
```

The result must construct its candidate from allowed prefix/log/proof data,
prove that candidate is the recovered same table, and derive the validator
checks. It must not assume `validWitness`, arbitrary access to the original
witness, a decoder's success, or that algebraic existential recovery is an
executable enumeration. Missing records, candidate omission, semantic
inconsistency, and resource exhaustion need proved exclusion or their own
explicit event. The current same-table decoder/semantic bridge and the
machine-readable [ExtractionGlobalDAG.json](ExtractionGlobalDAG.json) identify
these producers. Sharpening the obsolete extended layer cake is not needed
to make `earlyC1 = none` impossible, and cannot replace this extraction seam.
