# Before and after: event probability laws

Status: generic layers, measured composition (73120), simultaneous closed
synthetic witness (73123), and full finite adapter/corollary (73130) are checked.
Statement audit 73197 confirms the quantifiers printed below. Final axioms and
frozen import-manifest audits follow separately.

## Before — full existing event endpoint

`R1Z.PrivacyR1HeadlineDeployedEvents.privacy_headline_deployed_events`:

- `Env`, native `R`, acquisition `N`, common `S`: `Fintype` and `Nonempty`.
- `R0Z.mean`: rational finite uniform expectation (the handoff's
  “FsAbort.mean” is shorthand; the actual definition is `R0Z.mean`).
- D163: both uniform rational test means on the same common finite sample.
- Acquisition: exact joint equal law with the finite uniform `Env × R`.
- Conclusion: every observer and equal-public witness has distinguishing
  advantage at most `PV_EVH_Core.bound`; the numerical envelope and strict
  `< 1 / 2^100` are included in the same conjunction.

## After — exact probability expectations

`PV_MEAS_Deployed.privacy_headline_deployed_events_meas`:

- `Env`, native `R`, acquisition `N`, common `S`: arbitrary measurable spaces.
- Each law is a `Measure` with `IsProbabilityMeasure`, bundled by EXACTLY the
  subtype expression in pinned Mathlib's `ProbabilityMeasure` definition.
  Its topological API is not required.
- A decision probability is the nonnegative Lebesgue expectation
  `(∫⁻ s, ENNReal.ofReal (p s) ∂μ).toReal`, written `∫ₚ`. It is used on
  `[0,1]` decision probabilities, with finiteness and range proved. This is
  not an empirical mean or an approximation.
- D163: measurable coordinate maps, with BOTH exact pushforward marginals.
  The model coordinate retains its required finite uniform cryptographic law.
  The native and common laws need not have finite support or rational masses.
- Acquisition: a measurable map with exact JOINT pushforward law. A supplied
  environment-indexed native probability family is identified with that joint
  law by equality of expectations of bounded measurable tests (`ConditionalLaw`).
  Independence is not inferred. No disintegration-existence theorem for every
  arbitrary measurable joint space is claimed; this law identification is an
  explicit ordinary P obligation. It does not condition on success or remove
  any noise samples. The dependence of decision probabilities is measurable.
- Conclusion: the acquisition expectation versus the environment mixture of
  the SAME simE/completion decision probabilities is bounded by the SAME real
  cast of `PV_EVH_Core.bound`, strictly `< 1 / 2^100`.

## Exact finite specialization and unchanged obligations

`PV_MEAS_Legacy.links_of_legacy` constructs every measured link from the
old finite link conjunction, installing symbolic uniform measures. Thus the
new measurability and joint-law fields impose no extra finite-source premise.
`PV_MEAS_Legacy.finite_uniform_corollary` recovers the WHOLE original
rational statement, including its numerical envelope and strict threshold,
by the measured headline and exact expectation/cast identities. It never calls
the former headline theorem.

The observer TYPE is an alias of `PV_EVH_Core.Observer`; its adaptive program
and decision still consume `Signal × Observation A`. simE, completion, ordered
contexts, joint timing, public failure signal, bad event, seed/fuel charges,
all failed/divergent prefixes, nine source-event links, V400, causal prefixes,
observer-program association, selected callback and original three-field T
are retained. No native source or deployment row is discharged by this work.
Rows removed: NONE. No additional trust field or numerical error term.

`PV_MEAS_Satisfiability.closed_witness` supplies the full conjunction in an
explicit synthetic model, with external carriers and operations instantiated.
This proves consistency only; it is not an execution of the deployed prover
or a proof of a native link. The overall deployed privacy target is not yet
established.
