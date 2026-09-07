# Lean repair review: fixed-target theorem proved, adaptive coverage still open

Date: 2026-09-07. Research only. No selected protocol, verifier acceptance,
deployment manifest, production security claim or public-facing documentation
was changed. The user's accepted body allowance remains **40,282 bytes**.

## Decision

The supplied repair is a valid fixed-target direction. The essential finite
algebra and counting argument has now been kernel-checked, not just tested on
small fields. It bounds a different event from the disproved same-support
recovery claim. It does **not** replace that claim in the actual extractor yet.

The current q22 proposal remains **not certified** for 100-bit no-work security,
full-view ZK or matched complete-transaction CU. That is a decision about the
present evidence, not a general impossibility result for QM31 or V8.

Primary direction remains the 40,282-byte QM31 q22 query-aware reduction.
QM31 q23 is a separate 41,527-byte / +1,245-byte control, not an authorized size
increase. Full quintic q22 is the better-margin field-port fallback at 42,984
bytes / +2,702 bytes. Quintic q21 remains the thinner 41,692-byte / +1,410-byte
control. The conditional arithmetic in [coverage-review.md](coverage-review.md)
is unchanged; none of these is a completed protocol.

## Package and pinned context

Reviewed all four files before execution:
`/Users/dominic/Downloads/aspis_v8_lean_repair.zip`.
SHA-256: `bb72f95a73b112bdc9d6f29e635ac0234799def10ce698e7f5aeab6aa9edf712`.
The archive has four regular files, 29,663 uncompressed bytes, no executable
payload beyond the inspected Python standard-library script, and no Lean file.
Its work order refers to `cffcc740716f220435bd9a5da05b8fc349c8d3e7`.
An exact byte-for-byte copy is retained under
[experiments/lean-repair-package](experiments/lean-repair-package/README.md).

Research parent: `c69873c0d5e5b28daa583655040fb915d1e8c873`.
Cached Lean workspace: main `bff78d6eab006dfc75c704abde824fa7c57637b1`.
Provider/source audit: V8 branch `07b66afc22288a6ff460180242b73de4f341e02d`.
Main's untracked semantic-probability files, `.tmp` and CU results were left
alone. The separate V8 worktree was read only.

## The actual proved experiment

See [FixedTargetQuerySupport.lean](experiments/FixedTargetQuerySupport.lean).
All objects below are fixed before the sampled challenges and schedule:
received-minus-target component residual polynomials, legal chord denominators,
circle coordinates, and the reference target/fold relation. A residual on a
fibre is represented by four polynomials of degree at most d in gamma.

Let U be T fibres, C the J identically matching fibres, G the nonzero field
elements, A the whole field, and S a direct uniform q-subset of U, independent
of gamma and alpha. Let P mean **all pointwise folded residuals are zero** and
B mean S is not contained in C. The finite product count proves

```
count(P and B) <= (choose(T,q)-choose(J,q)) * (d*|A|+(|G|-d)*3).
```

The normalization to rationals is itself proved. With k = |K|,

```
b = choose(J,q)/choose(T,q)
e = d/(k-1) + (1-d/(k-1))*3/k
Pr[P and B] <= (1-b)*e
Pr[P]       <= b+(1-b)*e.
```

These are counts in a explicitly defined independent product experiment;
there is no random-oracle or adversary-resource theorem hidden in this statement.
In particular, it cannot be applied directly to the prover's adaptive final256,
nonce selection, repeated transcript attempts, or a conditioned compact sampler.
Analytically choosing one bad fibre from S does not reorder the actual protocol.

The theorem requires d <= |G|, 3 <= |A|, nonzero 4,x,y and chord denominators.
It proves fold nonzeroness via invertibility, rather than assuming it. The actual
slot order is `(x,y),(x,-y),(-x,-y),(-x,y)`, and the literal nested fold identity
is checked symbolically. Correlation across q queries costs no union bound here:
all-query success implies success at the one selected bad fibre.

For the example's k=(2^31-1)^4, T=262144, J=9557, q=22, d=28:

| Event / screen | Bits, display only | Status |
|---|---:|---|
| Old intermediate same-support failure, lower bound | 101.2462242116 | Different event; counterexample retained |
| All queries common, b | 105.1420996194 | Exact rational |
| Pointwise pass and wrong queried support | 119.0458036869 | Generic theorem plus exact parameter arithmetic |
| Total pointwise pass | 105.1420054893 | Same fixed-target scope |
| Add general Tag-73 rho cancellation | 105.1419386911 | Conditional algebraic screen, not terminal acceptance |

Probabilities are summed before taking logarithms. The companion script asserts
the exact inequalities against 2^-119 and 2^-105; floating values are display
only. No PoW bits are added, and no quantum claim is made.

## Theorem map and the counterexample

| Declaration / family | What is kernel-checked | Remaining boundary |
|---|---|---|
| `foldCoefficients_injective`, `foldedPolynomial_eval_literal` | Invertible four-slot map and exact source-shaped nested fold | Source/OOD legality and index-map bridge |
| `root_filter_card_le`, `two_stage_count` | Polynomial root count and exact d*a+(g-d)*t numerator | Fixed-before-challenge objects |
| `fixed_target_wrong_support_count` | Integrated wrong-support event; selects its own bad fibre | Does not choose an adaptive extractor target |
| `common_schedule_card`, `normalize_wrong_support`, `total_count_from_wrong_support` | Exact subset counting, rational normalization and total composition | Independent direct sampling experiment |
| `zeroExample_wrong_support_count` | Explicit root-product, repeated-four-slot residual against zero target | Concrete QM31 encoder/OOD/index packaging not assembled |
| `zeroExample_top_coefficient` | D coefficient is one off common fibres | Target is not a payment witness |
| `disjoint_exceptional_gamma_card`, `root_label_injective`, `root_label_range` | Disjoint-family count; all 7,072,436 integer labels distinct, positive, below p | Nat-to-QM31/root-family bridge not assembled |
| `same_support_recovery_impossible` | Large zero support plus extra value one contradict encoder root cap | Encoder cap/index map explicit, not re-proved for Rust |
| `shiftedBatch_root_count` | General q-query shifted scalar cancellation has at most q roots | Fresh rho, fixed prior/residuals, later relation repairs |

Thus milestone A's generic algebra/counting is proved. Milestone B has a
symbolic root-product instance, interval facts and encoder-cap obstruction;
it is **not** a single closed Lean theorem instantiating every actual QM31
encoding, circle-index and transcript hypothesis. The existing optimized Rust
counterexample and prior arithmetic facts are reused, not rerun unchanged.
Milestones C and D remain unresolved.

## Source correction: q, not automatically q-1

The package correctly labels its optional batch result as requiring a source
proof. Its 21/(k-1) term is valid for a fixed nonzero degree-21 residual batch,
including the shifted batch when the prior discrepancy is known zero.

The general Tag-73 equation is instead

```
prior - rho * sum(i=0..q-1, residual[i] * rho^i).
```

Its constant coefficient carries the prior relation discrepancy. With any
nonzero residual vector it is a nonzero degree-at-most-q polynomial, regardless
of the prior. The new generic proof charges **22/(k-1)** for q22. This is not a
fatal flaw in the fixed-target argument; it is the necessary source adaptation.

Pinned research `crates/aspis-core/src/v6_transcript.rs` samples gamma nonzero,
alpha0 over the whole field, then absorbs final256, derives queries, and samples
nonzero rho. `v6_query_batch.rs` uses shifted powers for Tag-73. Authentication
must fix the query residuals before rho even though the Rust callback runs later.
The existing `K1/V7Tag73JointQueryBatchSoundness.lean` also requires accounting
for later alpha repairs: terminal acceptance is not the same event as the rho
polynomial being zero. No q22 production verifier was introduced here.

The optional 396430 inventory in the numerical artifact is **eight recorded
categories**, not purely semantic error. Adding it gives a hypothetical
104.2667058229-bit screen, still excluding adaptive coverage, full composition,
primitive assumptions and privacy. It is not entered as a security certificate.

## Provider-none audit: no discarded branch is silently removed

The exact source-shaped provider at `07b66afc` is
`routedCounterfactualParsedK14Branch?` in
`K1/V8A100SchedulerNativeK14Provider.lean`. Its structural cases are:

| Path | Current accounting in this continuation |
|---|---|
| Gamma zero | Outside the stated ideal nonzero sample; actual retries/failures remain scheduler obligations |
| Replay oracle returns none | Filters include abort/out-of-fuel/response failure or literal gamma mismatch; actual accepted replay equality is required, not assumed from none |
| K13 `idealRejected` | Actual acceptance-to-ideal bridge and query-batch/later-repair errors required |
| K13 `queryPhaseFailure` | Query/list event must be bounded in the actual adaptive model |
| K13 `oneFoldReductionFailure` | Fold event must be bounded; old broad loss is not silently removed |
| K13 `initialListCapFailure` | Actual code, thresholds and list theorem applicability required |
| K14 `width29` | **Principal uncovered accepted discarded branch**; no admissible adaptive-target/cover theorem yet |
| K14 success | Existing certificate is exposed; success-only refinement does not bound the preceding cases |

`replayedProofAtGamma_of_returned` is an existing endpoint for normally returned,
matching-gamma runs. Restored/cached/advance execution paths still require the
source replay equalities before this endpoint applies. This is an audited case
inventory, **not** a new total source-level probability/extraction theorem.

The earlier relaxed-family result constructs at most 100 joint tuples above
38,228 symbols without the old decoder filter. That is useful but does not prove
that every post-challenge combined/folded candidate lies on one of their curves.
Its support premise is a lower bound, while b in a false-target query bound
needs an upper bound. Close targets require semantic/relation classification;
uncovered targets require their own accepted-error bound.

New falsifier: over F17's constant code, duplicate each non-common quadratic
coefficient tuple on **two** fibres. With T=8, J=2 and relaxed list floor 3,
all 4,913 component tuples have at most two matching fibres: the close family
is empty. Six gammas nevertheless give four zero combined fibres; three uniform
queries pass with exact probability 3/112. This is a small countermodel to
deterministic coverage from a close-list cardinality statement alone. It is
not the actual circle code, a QM31 attack, or a refutation of a properly charged
adaptive argument. The material difference from the prior toy is two exceptional
fibres per gamma, rather than one captured by the relaxed floor-two zero tuple.

## Executed checks and bounded next decision

- Supplied Python: exact full JSON match; 90 profiles, 6,246 literal identity
  checks, 149,856 gamma/alpha/profile cases, 2,250 bad-schedule checks.
  0.48 s, 18,415,616 B peak RSS, zero swaps, exit 0.
- Independent companion: five large-rational crosschecks, 19,683 small exact
  normalization cases, and the 4,913-tuple coverage countermodel. 0.19 s,
  22,396,928 B RSS, zero swaps, exit 0. [Results](lean-repair-results.json).
- Focused Lean leaf only, using existing main cache. Exact final command,
  output, source hash, failures/replacements and resource metrics are in
  [lean-repair-evidence.json](lean-repair-evidence.json) and its linked log.
  No package build, generated recurrence expansion, SBF rebuild or remote job.

Next deciding experiment: replace the **K14 width29 accepted-error accounting**
with a total query-aware classifier whose outcome is witness recovery, a
pre-challenge target/cover with proved coverage, or an explicitly bounded joint
bad event. Test both root-product constructions above. Stop any claimed
zero-byte repair if it needs `candidateMember`, full shared support, a target
chosen after gamma treated as fixed, or uncharged provider-none mass. If it
needs new verifier evidence, recalculate bytes/CU instead of calling it proof-only.

There is no reason to start a full CU build merely because this fixed-target
lemma is now proved. The current hash-count increase and unmeasured full
transaction costs remain unchanged. No new protocol prover-time/RAM or SBF
measurement is claimed; the timings above are research checks only.
