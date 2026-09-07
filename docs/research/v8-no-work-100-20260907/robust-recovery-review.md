# Non-polynomial recovery continuation: a bounded-corruption reduction

2026-09-07. Research-only, continuing `bf1a1cccbc99045f0bc85f775ec13c91626011b4`
on `research/v8-no-work-100-20260907`, without resetting it. Separate V8 source
is pinned at `07b66afc22288a6ff460180242b73de4f341e02d`. No production changes.

## Decision

**There is a new quantitative result for non-polynomial received words, but
not a complete V8 recovery theorem.** A close anchor reduces accepted executions
to a correct-image/correct-relation/same-final case, plus a proved small error.
The actual received word need not be a polynomial. For at most **9,301 corrupt
complete fibres**, the new causal-game error is **105.1452784160 bits**. It uses
2.825640201% of a `2^-100` budget before the remaining, unbounded terms.

This does **not** dispose of the high-J construction: its zero anchor has a
valid image and can have the correct ordinary relation claim. Its same-final
branch is specifically retained. The no-close-anchor case also remains.
Neither event has a new general probability upper bound here.

The secondary result is an executable **complete research relation suffix**:
canonical parsing, real SHA-256/Merkle openings, component quotient evaluation,
all four compact rounds, shifted query injection and carried image weights.
The verifier never receives the witness-side quotient vector. It is **not** a
complete payment verifier, a Rust-to-Lean translation, or a matched CU result.
All four final fixtures use nonzero ordinary public weights and the honest
ordinary scalar, computed before tau on the prover side; the T512 rejection
is therefore testing the added image discrepancy, not an already false
ordinary scalar. The zero-ordinary-weight preflight also passed.

QM31 q22 remains the primary mathematical research direction under **40,282
bytes**, not a release choice. The unapproved fallback remains quintic q22 at
42,984 bytes; q23 at 41,527 bytes remains only a bounded-family control.

## 1. Actual objects, prefixes and matching set

Let `T=262144`, `k=(2^31-1)^4`, and `q=22`. In the intended image-aware V8
experiment, C1's 26 base-field words are fixed before early challenges; C2's
three QM31 words may depend on lambda/chi. These are committed *words*, not
assumed code polynomials. Semantic challenges/responses and ordinary claims
must be retained in the prefix. The component-OOD interaction is sequential:

1. sample zeta0; absorb its 29 responses with vector index 0;
2. sample distinct zeta1 from the updated transcript; absorb its 29 responses
   with vector index 1;
3. absorb batch nonce, sample nonzero gamma; absorb inactive claim and derive
   its mixing challenge; determine ordinary weights/scalar and chord;
4. freeze those objects, absorb distinct image framing, sample nonzero tau;
5. receive six response0 coefficients, absorb fold nonce, sample alpha0;
6. receive final256 (allowed to depend on tau and alpha0), absorb final nonce,
   sample distinct queries, then nonzero rho;
7. three subsequent compact responses each precede their own fresh alpha.

The real proposed semantic-to-ordinary-weight construction is still missing
from this callback. It does not pretend the opaque semantic prefix executes
the selected payment zerocheck. The research suffix uses a distinct profile,
and explicitly hashes its *public* ordinary weights/scalar after gamma and
before tau. That binds supplied inputs but does not prove their semantic origin.

For an original circle point z, define the *virtual word*

`R_gamma(z) = (sum_l gamma^l C_l(z) - I_gamma(z)) / L(z)`.

Here I interpolates the gamma-batched OOD values using x, or y for equal-x
pairs, and `L=a+b*x+c*y`. Division is defined only when the chord denominator
is nonzero; the callback rejects otherwise. For each four-slot fibre in source
order `(x,y),(x,-y),(-x,-y),(-x,y)`, apply the actual normalized circle-to-line
fold. The final-domain coordinate is `u=2*x^2-1`.

The matching set is **exactly**

`Mset = {u : F(u) = Fold_alpha0(R_gamma at its four slots)}`.

It is not the V7 raw-word `consistencySet`. All later discussion uses this
quotient/fold set. No unproved V7-to-V8 classifier substitution is made.

## 2. New information about the matching distribution

Before tau, select a polynomial **anchor** Q in the 1,024-dimensional quotient
space, and a set B of complete fibres outside which *all four* R values equal
Q. This selection may depend on the entire earlier prefix, including gamma
and both OOD vectors. It must not depend on tau, alpha0, or queries. This is a
restricted near-polynomial class, not an assertion that every prefix has Q.

After alpha0, put `Fstar=Fold_alpha0(Q)`. The real folded word equals
`Fstar + noise`, with noise supported on B. The adversary may choose any
degree-at-most-255 F at this later prefix. If `F != Fstar`, then

`Mset ⊆ B ∪ roots(F-Fstar)`, hence **`|Mset| <= |B|+255`**.

This is the new geometric input to the query-last argument. It holds for
arbitrary values on B, even after all earlier adaptivity. It does not use a
lower agreement bound as an upper bound and does not require a family union.
`noisy_agreement_cap` and `noisy_schedules_cap` prove it symbolically in Lean.

For `F=Fstar`, noise need not vanish on sampled fibres. This is why the proof
does NOT reuse the exact-polynomial premise that matching finals imply zero
residuals. Instead, if the prior discrepancy is nonzero, the shifted batch
polynomial is nonzero regardless of those residuals.

Define `e=C-<w,Q>`, `E1=Q[1023]`, `E2=b*Q[1022]-c*Q[1021]`.
The actual image-weight boundary discrepancy is

`e - tau*E1 - tau^2*E2`.

Two new bounds result (ideal, conditionally fresh challenges):

* **Bad anchor boundary**, meaning `e != 0 OR E1 != 0 OR E2 != 0`:
  `epsilon_near(B) = (q+2)/(k-1) + 24/k + choose(B+255,q)/choose(T,q)`.
  This includes **image-valid anchors with a wrong ordinary claim**, not only
  the previously handled invalid-image class.
* **Different final**, even with valid image and correct ordinary claim:
  `epsilon_off(B) = q/(k-1) + 18/k + choose(B+255,q)/choose(T,q)`.
  This bound applies at every query prefix where `F != Fstar`.

The game allows each response to depend on all preceding challenges. Q is an
anchor, not a silently recovered witness. `NoisyGame` does not assume
`candidateMember`, `Width29CandidateOnCurve`, provider success, or exact
polynomiality of R. Its geometric and discrepancy interfaces are explicit.
The sparse algebra in `ImageCallbackInterfaces` proves the image boundary,
compact response boundary/evaluation, and signed query injection identities;
the remaining source interfaces are listed below, not claimed discharged.

For disjoint pre-tau bad/good anchor classes, use
`max(epsilon_near,epsilon_off)=epsilon_near`, not their sum. The different-final
predicate is later than tau; its per-prefix bound is uniform, so averaging
over earlier challenges is valid. This finite conditioning argument is at
the mathematical game level, not an implemented scheduler extraction theorem.

| Corrupt fibres B | Different-final match cap | New local bound in bits | Interpretation |
|---:|---:|---:|---|
| 0 | 255 | 118.4150374966 | Reproduces old restricted result; not a new global claim |
| 9,301 | 9,556 | 105.1452784160 | Useful non-polynomial near-anchor class |
| 10,980 | 11,235 | 100.0027312730 | Last B passing the **local-only** budget |
| 10,981 | 11,236 | 99.9999037264 | Local-only screen fails |
| 252,587 | 252,842 | 1.1467614347 | Original common-zero anchor: useless bound |
| 252,588 | 252,843 | 1.1466358996 | Paired common-zero anchor: useless bound |

The last passing B is not a proposed parameter change or release threshold.
Other justified errors consume budget. Exact reduced rationals and threshold
comparisons are generated by `robust_ledger.py`, not fitted floating estimates.

### Falsification before formalisation

`robust_geometry.rs`, optimized, exhausts all received noise words in a five
point F5 code, all nonzero affine final differences, and every q2 schedule.
It also maximizes agreement over the adaptive final choices. The new B+d bound
passes and is sharp. The tempting stronger bound M<=d is false: for `p=X` and
noise `[0,1,0,0,0]`, M={0,1}. One q2 schedule passes, while `choose(1,2)=0`.
This justifies the charged B term. These are code-geometry tests, not QM31
enumeration, a probability estimate at 2^-100, or payment forgeries.

## 3. Total accounting, without discarding provider none

Define A as actual verifier acceptance and X as the specified extractor
returning a *valid payment witness* within its declared resources. Source,
authentication and replay coupling failures must be split off first. Failure
to establish the coupling is a missing theorem, not an arbitrarily tiny error.

The existing provider/classifier sources are pinned under the separate V8
worktree's `AspisFormal/AspisFormal/{K1,Pool}`. The class names and order below
are the source audit, NOT a claimed new V8 scheduler theorem.

| Ordered outcome | When determined | Treatment in A AND not X |
|---|---|---|
| Actual abort, malformed input, sampler exhaustion | Actual execution endpoint | Not A; fail-closed checks needed; do not condition accepted law on a prover-chosen retry |
| Replay abort, fuel exhaustion, absent proof/response | The relevant replay endpoint, possibly after queries | `E_replay` if actual run accepted; not silently zero and not a prequery O |
| Zero/mismatched gamma or other restored challenge | At corresponding replay boundary | Ideal nonzero gamma excludes zero only in that ideal game; equality is supplied by an oracle wrapper in existing source, not automatic for an arbitrary restorer |
| K13 idealRejected | After pointwise checks | Can coexist with scalar-batched actual acceptance; account for shifted batching/later repairs, not discard |
| K13 queryPhaseFailure | P AND low matching count | P is postquery; low matching count alone is prefix-measurable |
| K13 oneFoldReductionFailure | Prefix with word, alpha0, final and decoder | Retained unless covered by a proved **V8 quotient** reduction; no raw-word substitution |
| K13 initialListCapFailure | Same prefix | Existing list hypotheses/field/domain bridges still required |
| K14 width29 failure | Same prefix in ideal full-oracle model | Principal outside-recovery event remains; source provider returns none |
| K14 certificate returned | After routing/replay | Not yet X: semantic/ownership validation and bounded extraction must establish X |
| Valid witness returned and checked | Extraction endpoint | X, hence outside target failure event |

Give replay failures precedence to make the table a disjoint diagnostic
partition. K13 follows the source's idealRejected/query/fold/list order, then
K14. The complete actual event remains defined when no decoding candidate is
returned. A root alone is not an available full-word decoder input.

Inside an ideal, correctly coupled relation execution, the new partition is:

1. no pre-tau anchor within B=9301: retain `U_no_anchor`;
2. anchor exists with bad boundary: new bounded class;
3. anchor has good boundary but F differs from its true fold: new bounded class;
4. good boundary AND same final AND extraction fails: retain `U_same`;
5. actual valid witness extraction: success.

Thus the new reduction leaves **strictly fewer cases than all arbitrary
non-polynomial received words**: bad-boundary close words and off-anchor
adaptive finals have quantitative treatment. It does not assert that cases
1/4 are rare. In particular, a scalar batched polynomial with a valid image
does not show 29 component polynomials exist. The finite <=100 family theorem
and own-support C1 descent may be used when their actual premises hold; they
do not imply anchor existence, compatibility or efficient decoding here.

## 4. Preserve the regressions

| Regression | New classification / remaining limitation |
|---|---|
| A: J=9557, 7,072,436 exceptional gammas | Same-support failure remains false; zero relaxed-family tuple remains. Its common-zero anchor is far, not in the useful near class. No new upper bound on accepted mass. |
| B: J=9556, paired exceptional fibres | No OOD-compatible relaxed member at the stated floor remains possible. The zero anchor is far. Neither OOD compatibility nor candidate existence is assumed away. |
| C: J=252843, 9301 others, 260428 gammas | Near zero anchor; altered finals are bounded, but good-boundary/same-zero-final remains `U_same`. The roughly 2^-107.156 subevent remains only a lower bound, not a forgery. |
| D: pre-OOD T512 | Old exact-invalid-image game reused. New callback checks real openings and rejects tested true and altered finals at terminal. No claim that every challenge rejects. |
| E: zero-fold/nonzero-image kernel | Earlier exact artifact retained; sparse weights are carried through response0, not checked only against final256. |
| F: prior/query cancellation and later repair | Compact/query identities now kernel-checked against the source-shaped formulas; q, not q-1. Rare legal collisions remain charged, not asserted impossible. |

Existing root-product, paired and high-J artifacts are reused, not rerun
unchanged. The reviewed package's mention of an optional full-degree
extension-root paired variant is not accompanied by a located, certified
implementation in this research directory; no claim to have replayed one.
Any such variant falls under the same far-anchor/no-cover obligation, not an
excluded predicate. See `adaptive-tail-review.md` and `joint-image-review.md`.

## 5. Source/event ledger and remaining budget

| Event | Fixing prefix | Fresh challenge/law | Exact local bound | Status and overlap |
|---|---|---|---|---|
| Nonzero image/ordinary boundary cancels | Before tau: Q,w,C,L fixed | tau uniform K* | 2/(k-1) | `image_nonzero_any`, root bound; conservative for constant-only error |
| First relation repairs nonzero boundary | Response0 fixed, after tau | alpha0 uniform K | 6/k | `Rounds`, compact boundary/evaluation identities |
| Adaptive different final matches all queries | Complete final prefix | Uniform distinct q-subset of T | choose(B+255,q)/choose(T,q) | New proved geometric cap, conditional on supported-noise anchor |
| Shifted scalar batch repairs prior/residual | Query values fixed before rho | rho uniform K* | q/(k-1) | `shifted_nonzero`, `shifted_degree`, new query-injection identity |
| Later relation repairs | Each response before its alpha | Three sequential whole-field draws | 18/k | Reused causal `Rounds`; adaptivity allowed |
| No close anchor, or good anchor/same final/unextracted | Different prefixes as above | Earlier challenges and extractor resources | **Unknown** | New reduction leaves mass explicit |
| Authentication/source/replay/semantic extraction | Actual source-specific boundaries | Actual primitives/restorations | **Unknown in the composed V8 theorem** | No fabricated numerical assumptions |

The old exact-image error is included at B=0; do not add it separately. Four
relation repairs are counted once. The historical numerator 396430 comprises
30500 semantic, 292800 lambda-copy, 73100 chi-copy, 1 mu-zero, 1 inactive-chi,
2 OOD-mix, 24 relation and 2 kappa-point categories. It is not one semantic
term. We neither add it mechanically nor subtract 24 and assume all remaining
categories port to the new OOD/chord/image transcript.

At B=9301, an exact *ceiling before unsupported terms* is

`R = 2^-100 - [24/(k-1)+24/k+choose(9556,22)/choose(262144,22)]`.

R is positive, about 97.174359799% of the target budget (display -log2 R =
100.0413523970). The actual remaining allowance is
`R - E_source - E_auth - E_replay - E_semantic`; those quantities are not
numerically established, so the global allowance is **null**, not R or zero.
The still-required raw condition is `U_no_anchor + U_same <=` that allowance.
This is a stated obligation, not an assumed tail bound used to advertise success.

### Fiat–Shamir and privacy are separate

The finite game uses genuinely fresh conditional challenges. For bounded
rejection samplers, ideal independent raw draws and permutation symmetry can
give uniform successful outputs; aborts have zero actual acceptance. This
does not prove the actual SHA transcript law. Its prequeries, nonce choices,
forks/restorations, retries, Q oracle calls and total running time require a
V8-specific resource-dependent compiler. No positive PoW contribution is used;
the suffix absorbs the three existing nonce fields without checking work.
Malicious nonce search is unrestricted in the pending FS analysis. No generic
BCS multiplier or additive tiny `E_FS` is asserted. No unlimited-search or
quantum security claim follows; 208-bit digests are not universal 2^-104 errors.

For honest image-valid Q, the two image functionals are zero, but individual
relation responses change with tau. Those responses are new public linear
measurements of witness/mask-dependent coefficients. Initial zero claims do
not imply unchanged full-view leakage. Adaptive OOD answers, final256 and
authenticated query openings must be included in a simulator/rank argument
with the actual masks. Fixed-schedule ranks and the public zero-salt fixtures
are **not** adaptive ZK evidence. Full-view simulation remains open.

## 6. Research callback and honest interface-completion table

`experiments/relation_callback.rs` links the pinned optimized `aspis_core` field,
transcript, gamma recombination, circle fold, WeightAccumulator and Merkle
implementations. A separate fixture module alone materializes Q and trees.
The callback uses canonical 16-byte fixed fields, six sent coefficients per
round in order `[c0,c1,c2,c3,c5,c6]`, reconstructing `c4=claim/4-c0`.
It freezes its public ordinary weights/scalar, derives tau, and carries the
image contribution without a dense image vector:

`terminal[3] += a1*a2*a3/256 * (tau*a0 + tau^2*(b*a0^2-c*a0^3))`.

Terminal indices 0..2 get no image weight. Query weight injection remains
separate and starts at rho^1. Real packed leaf data, salts, two typed roots and
minimal frontiers are checked. Canonical malformed fields, truncated bodies,
packed noncanonical queries, changed frontier/statement and bounded sampler
exhaustion are tested to reject. The wrapper never exposes a callback between
its weight binding and tau derivation. Its supplied ordinary values remain
trusted verifier-side inputs whose derivation must be connected later.

| Interface | Kernel-checked result | Actual Rust evidence / missing bridge |
|---|---|---|
| Exact quotient representation, natural tensor conversion | Existing theory only; no new complete encoder/source refinement | Fixtures coefficientwise divide T2/T512 by chord, convert Laurent to natural tensor basis and compare actual normalized openings with final256 evaluations. Not a universal translated theorem. |
| Degree <=255 and distinct final points | New game is generic over a finite **set** and degree-bounded difference | `domain_geometry.rs` checks all 262144 actual final points are distinct, all base x/y nonzero, and 256 tensor degree/leading-coefficient calculations. This is finite arithmetic verification; full Lean source-domain/encoder bridge still required. |
| Image boundary | `image_boundary` derives e-tau*E1-tau^2*E2 from actual sparse weights | Source installs matching sparse contribution; end-to-end differential fixtures |
| AfterFold.same_prior | `same_prior_dot`, exact compact convolution evaluation | Same final uses same carried weights; no false inference that noisy query residuals vanish |
| AfterFold.zero_iff and shifted sign | `eval_residual_zero_iff`, `query_injection` for real evaluation functionals | Slot order and source evaluation tested; WeightAccumulator/packed-decoder full translation missing |
| Each compact response | `sent_boundary`, `compact_error_boundary`, `compact_error_degree`, `compact_error_eval` for arbitrary n | Actual core convolution/folds in fixtures; source loop translation not claimed |
| Sparse image terminal and acceptance | `sparse_image_terminal`, `terminal_zero` | Global 1024-index sparse propagation previously differential-tested; actual suffix now uses it; no complete Rust-to-game constructor claimed |

Thus the algebraic round interface is proved without an assumed response
equality. The completed endpoint is an executable research relation suffix,
**not** a theorem that the actual payment verifier refines `NoisyGame`.

## 7. Bytes, operations and measured scope

Maximum canonical body remains **40,282 bytes**:

| Section | Bytes |
|---|---:|
| 697 QM31 fixed fields | 11,152 |
| Two 26-byte roots | 52 |
| Three retained 8-byte nonces | 24 |
| 22 x 621-byte authenticated records | 13,662 |
| Two maximum 296-node frontiers | 15,392 |
| **Total** | **40,282** |

Tau and both zero claims transmit zero scalars; no new round or padding was
introduced. Account/instruction/lifecycle bytes are not proof body bytes.
The wrapper's public dense-weight binding hashes 16,384 bytes, plus claim
and framing, but transmits none. This is **real extra verifier work**, not a
production optimization. Derived structured weights should eventually remove
this extra binding only with a source proof of their derivation.

Maximum q22 authentication remains 634 internal hashes plus 44 leaves;
selected V7 was 436 plus 32. This continuation does not compensate that cost.
The four new fixture suffixes measured respectively 606/606/600/606 internal
hashes, 701/701/695/701 total hash calls and 1336/1336/1330/1336 padded SHA-256
blocks. Inputs and results are in `evidence/relation-callback.log`. These are
operation counts, not SBF CU; the fixtures are not worst schedules.

The sparse image terminal source expression uses eight generic QM31 `mul`
calls, three `square` calls (including recomputed a0^2), and one base-scalar
multiplication; multiplying its result by final[3] adds one generic product.
This is a direct call census, not a base-product/CU substitution. There are
88 live quotient-denominator inversions at q22 in this simple callback, plus
point/chord and normalized fold work. It deliberately has no inverse-hint
optimization and no claimed CU parity.

The optimized field/core arithmetic and fixture run took **9.61 s**, peak
RSS **24,756,224 bytes**, zero swaps, for all four fixtures and adversarial
checks. The cached SHA2 backend was a debug dependency: do not call this a
release SHA benchmark, full Aspis prover time, or 2–5-second search result.
The fixture builds one nonuniform C1 tree and a compressed uniform C2 tree;
it is not a realistic full private-prover memory test. No search was used.

Host arm64 assembly has 1,200-byte own frame for `verify_relation` and
1,664 bytes for `opened_values`. A linked stable-sort helper reserves 4,176
bytes. These are **host frames**, not a bound on the whole call chain or SBF
frames. The complete callback's SBF stack/CU is unmeasured. No SBF rebuild or
complete transaction was launched. The isolated earlier stack-safe kernels
do not certify this callback.

Full local proving peak RAM, streaming time, disk/network traffic for a full
proof, and all four matched transaction CUs remain unmeasured. The small
fixture's memory use does not answer whether a complete prover avoids GiBs.

## 8. Evidence and one decisive next experiment

See `robust-evidence.json`, the two focused Lean leaves and their axiom logs.
All retained audited results use only propext/Classical.choice/Quot.sound;
no sorry or new axioms. Only focused cached leaves were compiled. Local proof
errors were fixed locally, including shifted-sum normalization; no broad
manifest, Aeneas, package build or memory-cap escalation was used.

**Next experiment:** on small actual circle codes, enumerate the remaining
good-image/good-ordinary-boundary/**same-final** accepted class with the
semantic weight construction installed, varying precommitted component words
and respecting sequential OOD timing. Test whether a weak, own-support
component recovery suffices for the *actual ownership/semantic checks*.
Include A/B/C, not just D. First falsify this implication before Lean work:
`near anchor + image valid + ordinary relation exact + same final =>`
`a compatible semantic component tuple on sufficient own support`.

Success means a non-circular component/extractor theorem or a quantitative
bound on the failed implication with its exact resources. A single compatible
but false-semantic close tuple is a stopping counterexample for that lemma;
classify it through a genuinely fresh semantic check, or cost the added check
before further formalisation. Do not widen the B cap or assume a 100-target
union to hide it. If the semantic relation cannot supply that implication,
q22 remains uncertified and the fallback requires an explicit byte relaxation.

This continuation stops at a new proved near-word reduction and an executable
relation suffix, with the global recovery, full-view ZK, FS and CU gates still
open. It is substantive progress, not a declaration that the user objective
has been achieved or that q22 is impossible.
