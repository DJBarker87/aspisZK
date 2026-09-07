# Focused Codex/Lean work order: query-aware recovery, not same-support recovery

Work from the reviewed `cffcc740716f220435bd9a5da05b8fc349c8d3e7` snapshot in an
isolated research worktree, first inspecting and pinning any current descendants.
Read AGENTS.md. Do not alter production or weaken the user's 100-bit/no-PoW-credit
security requirement, canonical 40,282-byte allowance or matched-CU requirement.
Do not launch a broad parameter sweep or whole-project replay to start.

## Goal

Attempt a proof-only repair of the reduction around the full-fibre counterexample.
The false 2,800-gamma unconditional same-support theorem is not a target. Keep
that example as a regression test. Prove a useful query-aware statement first,
then confront the genuinely missing adaptive/extractor coverage implication.

## Milestone A — a mathematical lemma, not more numerical decide facts

Generalise the report's fixed-target lemma over a finite field, fixed received
oracles, a fixed component target and a fixed legal OOD prefix. The target must
match the OOD component values and be fixed before gamma and alpha. Derive and
prove nonzeroness/degree of the selected fibre residual and invertibility of the
normalized arity-four coefficient map. Handle actual alpha sampling including
zero; use the nonzero variant only if that is really the candidate's sampler.

For uniform independent gamma, alpha and direct distinct q-query sampling prove

    Pr[folded query acceptance AND some queried component mismatches target]
       <= (1 - C(J,q)/C(T,q))
          * (d/(|K|-1) + (1-d/(|K|-1))*3/|K|),

and the associated total pointwise acceptance bound. Handle ordinary range
premises such as d <= |K|-1 explicitly. Use the finite root bound and count
query subsets symbolically. Do not enumerate |K| challenges or reduce huge
binomial terms in the kernel.

The first-bad-queried-fibre rule depends only on an independent schedule. Moving
that conditioning in the analysis does not permit changing the protocol order.
If final claims adapt to challenges, they do not satisfy the lemma's fixed-target
premise merely because the verifier checks them later.

Separately prove the powers-of-rho cancellation term with its exact residual
fixing boundary. Pointwise equality is not automatically the selected verifier's
one batched equality.

## Milestone B — instantiate this specific counterexample

Construct the zero component target explicitly for the reported fixed received
oracles and zero final polynomial. Prove the disjoint root intervals, D-column
mismatch and common query support. Show that the example refutes full-support
recovery while satisfying the new joint query-support bound. This is a formal
statement about that example, not recovery of an arbitrary valid payment witness.

Optional simpler algebraic cross-check: formalise the U(alpha)+x^2 V(alpha)
reciprocal-chord numerator identity in README.md and its at-most-one ordinary
fold-zero-fibre consequence. The main fixed-target bound is already slightly
sharper, so do not spend excessive effort optimising this auxiliary result.

## Milestone C — the deciding adaptive theorem

Inspect the actual scheduler-native partial provider and every reason it returns
none, including restored/cached/advance branches and earlier K13/K14 errors.
Build a total case partition of the real execution. For every accepted
continuation establish either actual witness recovery or membership in one of
an exhaustively enumerated set of bad events whose probabilities are proved.

The principal target is a bound on

    Pr[accepted continuation AND actual extraction failure],

not the provider's success-conditional error or Pr[provider returns none] alone.

Construct a permissible pre-challenge target/cover, or a genuinely adaptive
argument. Do not assume candidateMember, discard none branches from the
probability space, or reuse the old approximately 75-bit coherence success as
an uncharged prerequisite. Declaring a partial provider does not constitute a
probability bound. Classical choice is not a solution to dependence on future
challenges.

If a covering-family argument is used, prove its joint-tuple cardinality and
coverage of all relevant branches. A list bound on individual codewords is not
a bound on tuples. Charge family size and failed-cover measure. q23 can be
reported as a separate outside-budget control, not silently substituted for q22.

## Milestone D — actual composition only after coverage

Lift the proved events to the source-shaped Fiat–Shamir/master-tape experiment,
including adversary oracle probes, outer nonce choices, restoration forks,
query sampling, authentication and actual semantic/relation errors. No positive
security contribution from grind difficulty. State remaining primitive and
runtime assumptions honestly. Privacy remains a separate full-view obligation.

Only a proof for the unchanged candidate can be called a zero-byte proof-only
improvement. If repairing the theorem requires verifier changes or another
commitment/challenge/message, update the complete census and mark CU unmeasured.
A repaired soundness proof does not by itself offset q22's extra authentication.

## Formal workflow and reporting

Compile each small generic file, then its instance and bridge; reuse caches.
Audit #print axioms for every principal lemma and audit the actual hypotheses,
not only the absence of sorryAx. No new axioms or concluding security predicates
supplied as assumptions. Record exact toolchain, revision, command, result, wall
time and peak RSS. Distinguish kernel-checked statements, mathematical derivations,
finite tests and unresolved statements.

Deliver a short theorem map with:
- what is now universally proved and precisely instantiated;
- which provider-none paths are covered and which remain uncovered;
- the exact post-composition error budget when available;
- a counterexample to a failed generalisation, rather than a conditional theorem
  whose added hypothesis repeats the missing conclusion.

Carry out the focused proof attempt, but do not turn success on A/B into a claim
that C/D have been solved. Failure of this attempt is not a general impossibility
claim about V8.
