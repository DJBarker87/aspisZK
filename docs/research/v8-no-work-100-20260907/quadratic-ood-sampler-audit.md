# Quadratic cover: sequential OOD sampler audit

Status: source inspection and mathematical interface proposal only. No new
Lean theorem, compilation, probability certificate, or remote job was run.
Inspected source parent: `51692ed712ecb646b51e15e4b8e93e149a6b4014`.
The algebraic quadratic cover is already checked; its OOD sampling law is
not supplied by the existing ordinary-mix pair theorem.

## What is fixed, and what remains adaptive

[`SelectedQuadraticCover.fixed_cover`](experiments/SelectedQuadraticCover.lean)
constructs `E ≠ 0`, `E.natDegree ≤ 114687`, and a finite set `J` with
`J.card ≤ 936616` from the complete received C1/C2 words alone. It then
quantifies over both OOD parameters, both polynomial answer rows, gamma,
and the polynomial candidate U. Thus E and J are fixed before either OOD
point. Its conclusion for the same retained quadratic-factor root is

`(E(t0) = 0 ∧ E(t1) = 0) ∨ gamma ∈ J`.

No probability conditioning is needed to obtain this inclusion. In
particular, it does not require fixing U, Q, or the final message before
alpha. It does not assert that every accepted proof has a quadratic factor.
The higher-Y, tuple, and earlier exception alternatives must be preserved
by the surrounding event partition.

The current [`CausalCoveredRecovery.Execution`](experiments/CausalCoveredRecovery.lean)
fixes the entire OOD data record before its nested gamma/kappa/tau/alpha
averages. It is an appropriate suffix interface, not a model of the two
earlier OOD draws. An outer experiment must construct a different Execution
for each completed OOD prefix, with the same earlier c1/c2. The local
degree-two helper curve and all 29 gamma powers remain unchanged.

## Literal selected source order and aborts

The selected research entry is
[`inactive_row_binding.rs::to_gamma`](experiments/inactive_row_binding.rs),
lines 56–63. It does the following, in order:

1. Absorb all three ordinary 29-column point-claim rows.
2. Call `challenge_secure_circle_point` for the first point s.
3. Absorb `[0] || first_29_answers` under `V8_COMPONENT_OOD_VECTOR`.
4. Call `challenge_secure_circle_point` at most three times, accepting the
   first returned point unequal to s. A failed circle call aborts immediately;
   it is **not** treated as a duplicate and retried by this outer loop.
5. Absorb `[1] || second_29_answers` under the same vector label, then the
   first eight nonce bytes under `M31_PAYMENT_BATCH_POW_NONCE`.
6. Call the nonzero QM31 sampler for gamma.

The first answer may depend on the first point and its full history. The
second answer and nonce may depend on both points and their full history.
Neither answer is required to have been fixed before its own point. The
obstruction is nevertheless fixed earlier than both answers.

The source sampler layers must remain distinct:

- `challenge_qm31` gives each of four limbs at most eight 31-bit candidates,
  rejecting the single value P. Exhaustion of any limb is an immediate error.
  The word cursor is shared across limbs; a spent eight-word block is replaced
  by a fresh squeeze/advance, and unused words at function return are discarded.
- `challenge_secure_circle_point` permits three ordinary QM31 calls. An
  ordinary-call failure immediately propagates; a successfully decoded but
  inadmissible parameter causes the next circle attempt.
- The distinct-second-point wrapper permits three **complete circle calls**.
  Only a successfully returned duplicate point retries this wrapper.
- `challenge_nonzero_qm31` permits three ordinary calls; an ordinary failure
  aborts, zero retries, and nonzero returns.

This is not a nine-parameter flat retry for the second point. For example,
three inadmissible parameters in its first circle call abort the source even
if a later unused parameter would give a distinct admissible point. Flattening
the retries would incorrectly accept that tape. The OOD pair uses at most
12 ordinary calls (three for the first point, nine for the distinct wrapper),
each with at most four squeeze blocks. This is a local sampler inventory,
not a whole-proof hash budget or a grinding bound.

## Exact parameter domain and source-to-GRS coordinate

For K = QM31 and its embedded subfield C = CM31, the literal acceptance set is

`S = {t : K | t.im ≠ 0 ∧ 1 + t^2 ≠ 0}`.

The source first checks the denominator using `try_inv`, and only then checks
the CM31 condition. Its point is

`phi(t) = ((1-t^2)/(1+t^2), 2*t/(1+t^2))`.

On S, `1 + phi(t).x = 2/(1+t^2) ≠ 0`, so
`phi(t).y/(1+phi(t).x) = t`. Consequently phi is injective on S and misses
the west pole. This is exactly the coordinate required by
[`SelectedOODGate.point`](experiments/SelectedOODGate.lean), not the circle
x-coordinate. The latter is two-to-one: t and -t have equal x-coordinates
but distinct returned circle points. The distinct wrapper excludes only
the previous parameter t0, not both t0 and -t0.

Mathematically, the singular parameters are ±i, already in CM31: factor
`t^2+1 = (t-i)(t+i)` using the literal tower element i. Thus S = K \ C and
`N := |S| = P^4-P^2`. The cached exact tower supplies i and field/cardinality
facts. The small selected theorem deriving this accepted-domain equality,
the inverse parameter identity, and the returned-byte injectivity has not
been found as an exported combined sampler interface in this audit; it must
be proved before inserting that exact N into a source-connected probability
statement. Using the literal S and its cardinal N avoids assuming that bridge.

[`V7Tag73SecureCircleMap`](../../../AspisFormal/AspisFormal/K1/V7Tag73SecureCircleMap.lean)
already proves the actual check order, successful encoded x/y formulas, exact
canonical field encoding, and `successful_qm31TryInv_is_inverse`. These are
the appropriate algebraic inputs. `OODInterpolant.Data.Checked` alone does
not imply circle membership, west-pole avoidance, or parameter admissibility.

## Minimal new experiment, without independent labels

The smallest literal model should retain state/history and return `Option`,
with None contributing zero accepted mass:

`ordinary(h) → Option (t,h')`

`circle3(h)`: call ordinary; propagate None; apply the exact circle map;
return on success, otherwise recurse with remaining fuel and h'.

`distinct3(h,t0)`: call circle3; propagate None; return if t≠t0;
otherwise recurse with remaining outer fuel and the returned history.

Between the first and second calls, an arbitrary history-dependent prover
chooses answer0 and its actual absorb updates the state. After point1,
another such continuation chooses answer1 and nonce, then the nonzero
sampler runs. All internal rejected words, used blocks, and duplex-advance
answers remain part of the history. A completed proof record is not the
initial history of this model.

The necessary law is conditional freshness of the next raw block **at every
reachable sampling history**, or a proved finite fresh-tape equivalence
yielding that law. Distinct labels do not establish it. In the actual source,
`squeeze_block` queries `state || DOM_SQUEEZE` and then updates state using
`state || DOM_ADVANCE`; absorbs also hash the prior state. The source/ROM
coupling must account for earlier oracle queries, repeated inputs, adversarial
nonce trials and transcript selection. An arbitrary deterministic hash callback
is not a uniform sampling law.

As an unformalized check of the proposed literal model, suppose one fresh
ordinary call succeeds with probability s and gives each t∈K mass s/|K|.
Then one circle3 call has a constant success mass c across histories and
gives each t∈S mass c/N, where

`c = N*(s/|K|)*(1 + r + r^2)`, `r = s*(|K|-N)/|K|`.

For fixed admissible t0, distinct3 gives each t1∈S\{t0} mass

`(c/N)*(1 + c/N + (c/N)^2)`.

These expressions retain the immediate-abort behavior at both layers. The
joint mass of the ordered distinct pair is therefore constant on that
domain, with abort mass retained. This derivation uses fresh continuations,
not independence of labels, and is a target for a new bounded-sampler leaf;
it is not a checked theorem supplied by this report.

With `R = {t∈S | E(t)=0}`, m=|R|≤deg E, the resulting unconditioned pair
event is bounded by `m*(m-1)/(N*(N-1))`, hence by the same expression with
degree bound 114687. Sampler aborts only reduce accepted mass. The exact
number of ordered distinct root pairs is m*(m-1); a squared bound is a
safe weakening, not an independent-pair law. A fresh nonzero gamma slice
would similarly cost `|J\{0}|/(|K|-1) ≤ 936616/(|K|-1)`. Adding these
two bounds needs no independence between the pair and gamma.

These are proposed consequences of the specified fresh-tape experiment,
not a probability theorem for current accepted proofs. In particular, one
must not condition on OOD identities, the existence of a covered candidate,
semantic validity, successful extraction, or a favorable suffix and then
reuse fresh uniformity. The present causal reduction should retain the
unaveraged both-roots indicator until the outer law is actually connected.

## Reusable V7 interfaces and exact gaps

- `V7Tag73EightRetrySamplerLaw.successfulTag73OrdinaryExactLaw_eq_uniform`
  proves the successful eight-retry, four-limb law. Reuse it, including its
  shared-cursor stopping semantics, rather than substituting four padded
  independent limb outputs without a source equivalence.
- `V7Tag73SamplerDecoder.decodeSecureCirclePrefix` already models a
  three-attempt circle sampler with immediate ordinary-abort propagation.
  `V7Tag73IncrementalSamplerControl.decodeSecureCircleParameterExact_accepted_prefix_suffix_nil`
  provides exact accepted-prefix control. Neither is a uniform circle law
  or the new V8 distinct-second wrapper.
- `V7Tag73VariablePrefixGammaSampler.runGammaPrefix_matches_sampleChallenge`
  and `runGammaPrefix_unread_suffix_irrelevant` provide consumed-prefix
  semantics for gamma. `V7Tag73VariablePrefixGammaProbability.routed_skeleton_dependent_gamma_probability_le`
  gives the nonzero target bound on its successful routed experiment. The
  target can be the same pre-OOD J, but the V8 outer tape/event connection
  must still be constructed.
- `V7Tag73SuccessfulSamplerConditioningCore` (namespace
  `V7Tag73SuccessfulSamplerConditioningBridge`) exports
  `uniform_tape_dependent_successful_event_probability_le`: a total uniform
  tape is bounded via a successful-subtype experiment **only after** an exact
  coordinate equivalence and event inclusion are supplied. It does not
  license conditioning away any later verifier event. Its slice-averaging
  lemmas are reusable for the new literal model.
- `V7Tag73K15FixedSamplerProbabilityAdapters.sequentialUniformOrdinaryPairLaw_eq_uniform`
  and `duplex_ordinary_pair_dependent_probability_le` concern ordinary QM31
  **OOD mixing scalars**, not secure circle points. The old
  `V7Tag73TranscriptSchedule.oodEvents` is point/value/mix per row, and its
  `PreGammaTranscriptPrefix` puts those events after gamma/kappa. The V8
  component-point/answer pair is before gamma and has the new distinctness
  wrapper. Reusing the old complete prefix theorem here would be false.

The smallest worthwhile next proof is therefore the actual nested
`circle3`/`distinct3` successful-subprobability law, with the exact map
admissibility and parameter recovery bridge. A later finite-tape/source
coupling can consume it. No family-count multiplier is required for the
single E/J already constructed by the quadratic cover.

## Inspected source pins

Repository: `https://github.com/DJBarker87/aspisZK`, commit
`51692ed712ecb646b51e15e4b8e93e149a6b4014`. The following hashes were read
locally; this audit did not fetch or mutate a remote repository.

| Source | SHA-256 |
|---|---|
| [selected `to_gamma`](https://github.com/DJBarker87/aspisZK/blob/51692ed712ecb646b51e15e4b8e93e149a6b4014/docs/research/v8-no-work-100-20260907/experiments/inactive_row_binding.rs#L56) | `4642f1e4361aeb9f991ef917f8efdea292187fe3de9e3a9d351230859f9ad98b` |
| [core transcript sampler](https://github.com/DJBarker87/aspisZK/blob/51692ed712ecb646b51e15e4b8e93e149a6b4014/crates/aspis-core/src/transcript.rs#L378) | `be036d144b9fe0c8119d9f6fdd8ca2167d1379f7d1d785fa2f197200b9f7d119` |
| [secure circle map](https://github.com/DJBarker87/aspisZK/blob/51692ed712ecb646b51e15e4b8e93e149a6b4014/crates/aspis-core/src/circle.rs#L55) | `8f6f0f32c8dd93e3ee459df0c1d0ef710b01996d3bc929dbeffb3f7d14a0227c` |
| `experiments/SelectedQuadraticCover.lean` | `e4d3b6b14119b2116cd770bf4c24a745e614a640e910a33e454d16b70ad912b9` |
| `K1/V7Tag73SecureCircleMap.lean` | `6b3497ca6a87bbb87f71653a25a419745b65123eec769156ff33ba6cd2669070` |
| `K1/V7Tag73SamplerDecoder.lean` | `e5bdf7fb6513decec05bdeb54789f1ab35541c2389aab2f9ec0339f2dc14aa14` |
| `K1/V7Tag73EightRetrySamplerLaw.lean` | `dfb490b1bfbce4abe894e1809ec8d933acb55dbc5f6e5eb1de5b6942e5b5941e` |
| `K1/V7Tag73VariablePrefixGammaSampler.lean` | `5395e710e188f1f7e2085fbf84304fd040215446be7349d75061a540e22dea1f` |
| `K1/V7Tag73VariablePrefixGammaProbability.lean` | `70fbddb7dd82defb2860417f44443a1021106b6c44949b442f4d0bc1fb54c284` |
| `K1/V7Tag73SuccessfulSamplerConditioningCore.lean` | `12405b846c3198ce3f8917e1ba3d677ffed157c64feefb1ffeecc8ae893b52e7` |
| `K1/V7Tag73K15FixedSamplerProbabilityAdapters.lean` | `8aac8259b8d9800e3c3d3dfc1d634045ae6212967d6582c07a9301d1a73ab8cb` |

K1 paths above are under `AspisFormal/AspisFormal/`. These are source-map
pins, not new compiled-output provenance. Existing green artifacts and
other agents' files were left unchanged.
