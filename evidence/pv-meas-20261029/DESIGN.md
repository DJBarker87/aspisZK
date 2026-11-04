# Preregistered measure strengthening

Base: 946718387d, branch codex/pv-meas-20261029. New modules only,
prefix PV_MEAS_. No PV_EVH_ source changes. Budget: 100 Lean, zero native,
zero Kani; IDs 73100–73196 focused, 73197–73199 audit/replay.

## Target fixed before proof work

`privacy_headline_deployed_events_meas` is to quantify over arbitrary measurable
spaces Env, R, N and S and probability measures on them. Acquisition may be a
measurable map from any measured N, with its EXACT JOINT pushforward law; neither
finite support nor uniformity nor rational-valued atom masses is required.
Environment-indexed coupling laws may depend on the environment. In particular,
the actual native acquisition is not assumed independent merely by giving its
coordinates separate names. An exact joint law or a probability kernel must carry
that dependence. The final adversary decision is measurable on the same
`Signal × Observation A` as PV_EVH_Core.Observer; its adaptive OProg is unchanged.

Write p_real(e), p_ideal(e) for conditional decision probabilities. The target is

    |∫ e, p_real(e) dμEnv - ∫ e, p_ideal(e) dμEnv| ≤ (PV_EVH_Core.bound … : ℝ),
    (PV_EVH_Core.bound … : ℝ) < 1 / 2^100.

The left real integral is transported to the actual acquisition measure by an
exact pushforward equality, not by conditioning. The numerical envelope is the
same cast of the old rational envelope. The simulator is unchanged simE followed
by the SAME Completion; full ordered observations, all failure/divergence prefixes,
original bad event and exactly the original three-field T remain unchanged.
No noise coordinate becomes public information for the adversary.

## Named proof stages

1. `average_bound`: for arbitrary probability μ and integrable real p,q,
   pointwise |p(e)-q(e)| ≤ ε implies |∫p-∫q| ≤ ε. A measurable [0,1]-valued
   decision probability supplies integrability; no integrability premise should
   hide a boundedness restriction on timing or trace length.
2. `expectation_eq_of_equal_laws`: measurable maps with equal pushforwards give
   equal real expectations of measurable bounded decisions, by integral_map.
3. Generalise the native side of D163 to a measured common S with exact
   native and model marginals. The model coin carrier remains its existing finite
   uniform carrier, as REQUIRED by the cryptographic pointwise theorem. This
   does not impose any finite carrier on native R/S or the environment.
   The old `PV_EVH_Core.privacy_headline_events_model` itself still quantifies
   Fintype R, so merely feeding it into stage 1 does NOT complete this stage.
   Transfer its finite MODEL bad-event estimates through the model marginal,
   and prove the native/model bounded-test inequality over measured S using
   the original off-bad event context/timing/signal links.
4. Reuse the existing per-environment MODEL-versus-simE bound; combine with
   stage 3, then average and transport. Retain all deployed source links as P.
   Provide a simultaneous model witness if a new link skeleton is introduced
   (ruling v); do not label an unwitnessed skeleton verified.
5. `finite_uniform_corollary`: install the uniform finite measures, prove their
   integrals are the real casts of FsAbort.mean, and recover the full old
   rational theorem by exact cast/order transport. Not just an invocation of
   the old theorem with a new name.

## Before and after / ledger effect

Before: PV_EVH_Average.average_bound and deployed Runtime require Fintype
Env/R/N/S and use rational uniform means. Exact acquisition is a finite uniform
product; OwnedLaws.no_unbounded_environment exhibits the representability limit.

After (target, not yet a checked result): Env/R/N/S arbitrary measurable spaces
with arbitrary probability laws and exact marginals; real expectations replace
rational uniform means. Cryptographic model coins retain their existing law.
Native law identification, D163/D166, V400, causality, observer program,
source-event associations and selected callback remain ordinary obligations.
Rows removed: NONE. This strengthens representability; no native row is discharged.
No new T field, observer restriction, bad-event enlargement or bound term.

## Authority preflight

The inherited external authority has 5,673 entries and ZERO MeasureTheory or
Probability modules (external-authority-gap.json). Under common ruling h4 a
module absent from this authority is a stop for that step. Required first imports
are Mathlib.MeasureTheory.Measure.ProbabilityMeasure and
Mathlib.MeasureTheory.Integral.Bochner.Basic. No compiler has been launched and
no unauthorized external object loaded. An extension to the pinned Mathlib
closure has been requested. Source inspection and proof drafts can proceed;
they earn no checked theorem credit until the authority gap is resolved.
