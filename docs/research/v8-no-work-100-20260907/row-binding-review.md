# Continuation: separate the inactive claim from the first point row

2026-09-08. Research only. Base revision `f8c2f7a949fdbb31431a104c8d29d34195594d98`,
on `research/v8-no-work-100-20260907`, preserving its newer work beyond the
requested `bf1a1ccc` checkpoint. Separate V8 implementation remains pinned at
`07b66afc22288a6ff460180242b73de4f341e02d`. No production source, defaults,
acceptance path, main branch, deployment or public security claims changed.

## Decision: a concrete obstruction and a byte-neutral local repair

**The unchanged ordinary batch does not establish the point binding needed by
semantic extraction.** Its inactive claim and first point row both have
coefficient one. A prover can cancel a false first-row claim with the inactive
claim before kappa is drawn. This is not a rare polynomial collision.

The existing conditional theorem is not disproved: the header of
`AspisFormal/Pool/V7InactiveClaimBinding.lean` already explains this collision
and requires `inactiveExact` separately. The new result is an executable
semantic-and-authenticated-relation falsifier of deriving that premise from
aggregate equality, including a genuinely non-polynomial received word.
It is **not a tested production payment forgery** or a bound on failure to
extract every possible valid witness for the public statement.

An isolated research control separates the four claims with powers
`[1,kappa,kappa^2,kappa^3]`: inactive keeps coefficient one, all three point
rows move to `[kappa,kappa^2,kappa^3]`. It uses the existing challenge, no new
body values, and one additional QM31 multiplication to prepare kappa cubed.
Its **joint** noisy-word/relation/query bound is kernel-checked, without
`inactiveExact`. This closes a newly exposed class within the previous
good-aggregate/same-final remainder, not general component recovery.

Keep corrected QM31 q22 as the primary research direction under **40,282
bytes**. A proof-only completion of the unshifted batch cannot rely on this
false implication. Larger fields or q23 do not repair deterministic
constant-coefficient cancellation either. The size-relaxation controls remain
unapproved; no candidate is a release choice.

## 1. The source-shaped causal construction

The source assembly is `crates/aspis-core/src/v6_transcript.rs`,
`finish_onefold_relation`'s preparation around lines 707–735:

```
gamma <- nonzero challenge
read and absorb inactive_claim
kappa <- nonzero challenge
scales = [1, kappa, kappa^2]
C = inactive_claim + row0_gamma + kappa*row1_gamma + kappa^2*row2_gamma
w = inactive_mask + mle(z) + kappa*mle(successor(z)) + kappa^2*mle(xor12(z))
```

No independent inactive equality check was found in that preparation/path.
The V8 continuation retains this ordinary functional, but changes the OOD
order and quotient relation as specified below. We do not equate its
quotient/fold matching set with the V7 raw-word consistency set.

`experiments/inactive_row_binding.rs` links the actual optimized selected
pair-forest transfer **and withdrawal** terminal functions. The fixture:

1. Commits zero C1. Samples lambda/chi, then commits C2. The simplest C2 is
   also zero. No word is changed after commitment.
2. Sends zero initial mask claim and ten zero compact degree-27 semantic
   responses. Each missing coefficient is reconstructed by the source
   boundary equation; the running terminal is zero. Challenges z are causal.
3. Evaluates the actual selected semantic terminal on zero point claims to
   obtain `T0`. Where the actual linear G-mask factor `g(z)` is nonzero, sets
   only row0 G to `d=-T0/g(z)`. The tested d values are nonzero. The selected
   terminal now equals zero, despite committed G being identically zero.
   This is a false point claim; nonzero off-cube `T0` alone is NOT a proof of
   an invalid Boolean trace.
4. Absorbs all 87 point claims, obtains zeta0, absorbs its zero 29-vector,
   then obtains distinct zeta1 and absorbs its zero 29-vector. Samples
   nonzero gamma after the existing batch-nonce field.
5. Sends `inactive_claim=-gamma^27*d` BEFORE kappa. The unshifted C is exactly
   zero for every kappa. The zero anchor Q, interpolant, image residuals and
   final256 are zero. All four sent compact relation responses can be zero.
6. Runs the actual authenticated openings, normalized fold, shifted rho
   injection and sparse carried image terminal through the research suffix.

The selected conditional source bridge cannot supply `inactiveExact` here:
its anchor-side inactive functional is zero and the transmitted scalar is
nonzero. The zero tuple itself is available, so this issue is not restricted
to provider `none` or K14 width29 failures. Recovery of some tuple is not
enough to bind that tuple to the semantic point claims.

### A genuinely non-polynomial version

Half the fixtures instead precommit D=1 on all four slots of fibre **17** and
zero elsewhere; H, G and C1 remain zero. This fibre is chosen before C2's
root, not after seeing queries. The virtual quotient

`R_gamma(z) = (sum_l gamma^l C_l(z) - I_gamma(z)) / L(z)`

equals the zero anchor on every other fibre, and is nonzero on fibre 17 when
the chord denominators are legal. Its more than 1,024 zeros and nonzero
values exclude a global polynomial in the quotient space by the existing
circle root bound. This uses that bound; it is not a new translated Lean
encoder proof. A forced-opening diagnostic authenticates fibre 17 and
checks its normalized residual is nonzero for the tested fold challenges.
The actual transcript schedules are not replaced by that diagnostic.

Conditional on a complete legal prefix and genuinely fresh uniform distinct
queries, the chance of missing this fixed fibre is exactly

`choose(T-1,22)/choose(T,22) = 131061/131072`, `T=262144`.

This is a schedule probability, **not** an unconditional production
acceptance probability: earlier legal-prefix conditions and source/FS
correspondence remain separate. It illustrates why a near-word/same-final
case with a false ordinary point claim cannot be dismissed by query sparsity.
There is no honest-prover search, rejected-seed retry, witness, or security
credit from work in this construction.

## 2. Repair, and the new joint theorem

Let Q be an anchor chosen **before kappa**, agreeing with R on all four
slots outside at most B fibres. R itself need not be a polynomial. Define
the reconstructed original polynomial `U=L*Q+I`. For an image-valid Q, let

```
i  = claimed_inactive - inactive_functional(U)
ej = claimed_gamma_batched_point_row_j - U(point_j), j=0,1,2.
```

All four errors must be fixed before kappa. They may depend on gamma, the
sequential OOD responses and earlier semantic messages. The repaired
ordinary discrepancy, after exact chord transport, is

`P(kappa)=i+kappa*e0+kappa^2*e1+kappa^3*e2`.

`RowSeparatedImageGame.rowPolynomial_eval`, `rowPolynomial_nonzero` and
`row_root_cap` establish the exact identity and at most three roots whenever
any error is nonzero. No separately authenticated inactive claim is assumed.
The construction's special error becomes `(kappa-1)*gamma^27*d`: kappa=1 is
a legitimate collision. Tests and theorem do not demand rejection there.
Choosing the inactive claim *after* kappa defeats this repair too; the small
exhaustive test retains that timing falsifier.

The substantive endpoint is `row_separated_joint_bound`. After kappa, each
strategy may adapt its response to tau, then alpha0, choose final256
adaptively, and adapt later responses to previous challenges. It instantiates
the existing noisy-word game, rather than stopping at a batching root count:

```
Pr[relation-game acceptance AND a pre-kappa ordinary coefficient is wrong]
 <= (q+3)/(k-1) + 24/k + choose(B+255,q)/choose(T,q).
```

The theorem is stated for every fixed nonzero error tuple; restriction to
that prefix class and averaging gives the event reading above. Its hypotheses
are a pre-kappa image-valid anchor, B-supported noise, degree-255 final
difference, exact discrepancy/terminal interfaces and the ideal conditional
challenge laws. They are NOT universal recovery or Rust correspondence
premises already discharged by this file.

An anchor, when it exists, may be selected mathematically from the finite set
defined by R and its distance alone, before kappa. There is no need to assume
uniqueness, to select from an adaptive post-kappa final, or to assume all
prefixes have such an anchor. This nonconstructive selection does not supply
an efficient extractor. Allowing Q to be selected after kappa would invalidate
the polynomial root argument and is explicitly outside the theorem.

For image-valid anchors with a nonzero ordinary discrepancy, tau cannot
cancel that constant discrepancy. `valid_image_wrong_ordinary` consequently
charges no spurious two-root tau term. It still permits tau-dependent
responses and charges all four relation repairs, once.

| B | New local joint bound (display bits) | Meaning |
|---:|---:|---|
| 0 or 1 | 118.3852901532 | New wrong-row class, not global security |
| 9301 | 105.1452753728 | Close non-polynomial class |
| 10980 | 100.0027311868 | Thin local-only threshold; not a release parameter |
| 10981 | 99.9999036404 | Even this local bound misses 100 |

All comparisons with `2^-100` use exact rationals in `row-binding-results.json`.
Floating logarithms are display only. The new result does not redo or rename
the previously proved 118.415-bit exact-invalid-image theorem.

## 3. Total accepted-execution accounting

Let A be actual verifier acceptance and X a specified resource-bounded
extractor returning a checked valid payment witness. Retain the ordered
replay/provider partition in `robust-recovery-review.md`, section 3:

| Outcome, in precedence order | Measurability and treatment |
|---|---|
| Actual malformed/abort/sampler exhaustion | Actual endpoint: not A if fail closed; do not confuse with replay abort |
| Accepted actual run, replay abort/fuel/missing response | Replay endpoint, possibly after queries: retain `E_replay` |
| Zero or mismatched restored challenge | Its replay boundary: retain mismatch/coupling obligation; ideal nonzero law is not a restorer theorem |
| K13 rejection/query/fold/list cases | Rejection and query success are postquery; low count and final/decoder classes can be prefix-measurable. Scalar acceptance can survive pointwise rejection. Retain batching/repair or unproved V8 quotient bridge as applicable |
| K14 width29 failure | Decoder prefix, not assumed equivalent to no near anchor; retain uncovered mass |
| Provider returns a certificate | Still not X until point/semantic/ownership binding and resource-bounded witness validation succeed |
| Checked valid witness returned | X, hence excluded from target failure |

These are diagnostic source cases, not a new total translated scheduler.
Unproved source correspondence is a missing theorem, not a tiny assigned
failure probability. No actual accepted execution is deleted because a
provider returns `none`.

Within a correctly coupled ideal relation game the *repaired* partition is:

1. No pre-kappa anchor within B: retain `U_no_anchor`.
2. Anchor has invalid image: reuse the image/noisy bound, even though its
   ordinary discrepancy depends on kappa. Condition before tau, not on an
   image-check outcome.
3. Image valid but `(i,e0,e1,e2)` not zero: **new joint bound**.
4. All four coefficients correct but actual final differs from Fold(Q):
   reuse `noisy_off_final_bound` uniformly at its later prefix.
5. All four correct, same final, but no valid witness extracted: retain
   `U_aggregate_correct`. This still includes component-wise membership,
   gamma-adaptive point binding, semantics, ownership and extractor cost.
6. Valid witness extraction: success.

Cases 2 and 3 are disjoint before kappa for a fixed anchor selection. Case 4
has a uniform later-prefix bound. Their combined ceiling is the maximum,
not the sum, of the applicable bounds; the new `(q+3)` bound dominates the
old `(q+2)` and off-final bounds. This averaging/partition step is explained
here, not claimed as a translated complete-verifier theorem.

This strictly refines the previous `U_same`: false *gamma-batched* row or
inactive values are now charged, without `inactiveExact`. It does **not**
infer the 87 component point equalities from three batched row equalities.
The anchor may still depend on gamma, so a pre-gamma fixed-target lane-root
bound cannot retrospectively be applied to it. No 100-target union is used.

## 4. Event ledger and budget

| Event | Fixing prefix; fresh law | Exact charge / status |
|---|---|---|
| Wrong four-coefficient ordinary batch cancels | Q,U,point claims,inactive before kappa; uniform K* | 3/(k-1), new root theorem |
| Invalid-image mixing cancels (other prefix class) | Q,w,C before tau; uniform K* | 2/(k-1), reused, **not added** to preceding class |
| First relation repairs discrepancy | response0 before alpha0; uniform K | 6/k |
| Different final agrees at all queries | actual final and folded word before queries; uniform distinct q-subset | choose(B+255,q)/choose(T,q) |
| Shifted query batch cancels | actual query residuals and prior before rho; uniform K* | q/(k-1), not q-1 |
| Three later relation repairs | each response before its fresh whole-field alpha | 18/k |
| No near anchor / aggregate-correct unrecovered | prefixes/extraction endpoints above | Unknown, retained |
| Authentication, actual source coupling, replay/resource and remaining semantic errors | Actual protocol-specific experiment | Unknown in global V8 composition |

At B=9301 the exact ceiling before unsupported terms is

`R=2^-100-[25/(k-1)+24/k+choose(9556,22)/choose(262144,22)]`.

The required condition is `U_no_anchor + U_aggregate_correct <= R` **minus
every justified remaining raw error**. Their numerical values are missing;
the actual global remaining allowance is `null`, not R. Four degree-six
relation repairs are charged once. The historical 396430 inventory is not
added or relabelled as semantic error; in particular its old kappa-point and
inactive categories cannot justify this changed joint event.

This is an ideal **classical** causal experiment. The callback absorbs the
three existing work nonces but does not check their work. They provide zero
security credit. SHA prequeries, chosen nonces, retries, forks/restorations,
oracle-query counts and total adversary/extractor time require a separate
V8-specific resource-bounded Fiat–Shamir theorem. No numerical compiler
bound, unlimited-search security, or quantum claim is established here.

## 5. Callback, interfaces, cost and privacy

The new entrypoint is isolated behind `--cfg v8_inactive_binding` in
`relation_callback.rs`. Default fixtures are unchanged. This entrypoint now
derives ordinary weights from actual statement points and the selected
compiled inactive-mask tables, rather than taking an arbitrary ordinary
functional from its caller. It freezes the ordinary scalar/weights, binds
them, derives fresh nonzero tau, requests compact response0 before alpha0,
and carries the existing sparse image terminal. The verifier never receives
the witness-side Q vector. Image claims still transmit no values.

It is **not the production verifier**: the public-context preamble is
synthetic; the complete statement/deployment/account preamble, work checks,
pool settlement and extraction are not executed. The copied compact semantic
grammar and chord transpose are source-shaped differential code, not an
Aeneas translation. This distinction is necessary even though the selected
terminal, field, folds, transcript and Merkle kernels are actually linked.

| Interface | Status after this continuation |
|---|---|
| Ordinary scalar/weight origin | Actual point and compiled mask kernels now used in research callback; no `inactiveExact` assumed |
| Shifted ordinary discrepancy polynomial | Kernel-checked `rowPolynomial_eval`; actual callback assembly tested; full encoder/chord bridge not newly translated |
| Exact polynomial quotient/fold degree and domain | Prior coefficient tests and exhaustive domain evidence reused; generic game set/degree hypotheses remain explicit |
| same-prior / zero-residual equivalence | Prior `same_prior_dot`, `eval_residual_zero_iff` and actual opened-value tests reused; no complete Rust-to-Lean extraction |
| Compact boundaries, query sign, image weights, terminal discrepancy | Prior `ImageCallbackInterfaces` identities reused; executable full suffix carried to terminal |
| Semantic terminal | Actual selected transfer and withdrawal functions executed; no complete honest payment proof generation or semantic source refinement |
| Complete source endpoint | **Not complete**. No claimed endpoint hides the remaining equality/coupling premises |

Maximum canonical body remains
`697*16 + 52 + 24 + 22*621 + 2*296*26 = 40,282` bytes.
No extra claim, nonce, padding or round is introduced by shifting kappa powers.
Largest fixture body was 39,866 bytes because its actual frontiers were
smaller; the maximum is not replaced by that observation. Proof-account,
instruction and lifecycle overhead is outside this body census.

Compared with the *same research ordinary assembly*, preparing kappa cubed
adds one QM31 multiplication. The same three scaled MLE components and mask
component are retained. This is NOT the total difference from selected V7:
the experimental callback still materializes and transposes dense weights,
and hashes 16,384 public weight bytes plus its scalar before tau. That binding
is not a hidden transmitted proof value, but its computation/transcript cost
is real. A structured binding/refinement is needed before a practical verifier.
Matched q22 maximum authentication still has 634 internal and 44 leaf hashes
versus selected V7's 436 and 32. Full-transaction CU delta is **unmeasured**.
Host AArch64 prologues reserve 3,376 bytes for `prepare`, 784 for `relation`,
and 1,600 for `semantic`. The fixture runner reserves 7,744 bytes and a
stable-sort helper 4,176 bytes. These are own-frame observations, not a
whole-call-chain bound or SBF stack evidence; this is not an SBF-ready build.

The shift and tau alter witness/mask-dependent relation responses. Even for
honest zero image claims, equal body size and invertible nonzero point scales
do not prove identical joint leakage. A simulator must cover adaptive OOD
answers, all changed compact responses, final256, point claims and openings.
Public zero salts and synthetic fixtures provide no full-view ZK evidence.

## 6. Regressions, executed evidence and next stopping condition

Original A and paired B root-product cases remain far-anchor cases for the
useful B=9301 ceiling. Their rejected same-support arguments stay rejected.
High-J C still has a near, image-valid zero anchor; its aggregate-correct
same-final component-recovery branch remains. Its approximately 2^-107.156
subevent is a lower bound, never a replacement upper bound. D's T512 image
obstruction, E's zero-fold/nonzero-image kernel, and F's shifted-query/prior
and later-repair collisions are reused within their established scope.
No unchanged heavy regression was rerun. The optional uncertified
extension-root paired variant remains uncertified, not silently discharged.

New execution: 32 unshifted semantic-plus-authenticated-relation fixtures
accepted false G(z) claims; 32 shifted controls rejected, across eight fixed
seeds, both operations and polynomial/non-polynomial words. This took 0.92 s,
3,375,104 B peak RSS, zero swaps. These are fixture execution costs, NOT
honest proving time or a universal attack rate. Exact optimized small-field
checks cover 17,744 nonzero error tuples, sharp three-root cases and the
late-inactive timing failure. Universal root/joint results come from Lean,
not the number of tests.

The focused `RowSeparatedImageGame.lean` leaf passed in 30.28 s, peak RSS
5,455,380,480 B, zero swaps, only standard `propext`, `Classical.choice` and
`Quot.sound`; no new axioms or `sorry`. A missing RobustImageGame olean was
materialized from unchanged source in the existing cache; no package replay,
Aeneas, SBF, remote or deployment job ran. See `row-binding-evidence.json`
for exact commands, hashes, limitations and initial cache-path correction.

**Single next experiment:** attack/prove the remaining gamma-level component
point-binding implication after the repaired row batch: a pre-kappa close
image-valid U agrees with all three gamma-batched point claims and the
inactive functional, but no semantic-compatible component tuple is available.
Start with exact small-code adaptive gamma searches retaining A–C, not
another kappa root lemma. Success requires a non-circular quantitative
bound for accepted such branches, or a precise new falsifier plus a costed
check. Stop pursuing a proof-only unchanged-grammar route if it again needs
to assume individual point binding or candidate membership. Do not expand
formal release/SBF work until that and full-view hiding have a viable path.
