# Causal row/image execution, early C1 identification and selected path

Research continuation from `15e73e9fdf529a0d0ab46353b98bccaf029bf4f5`, on
`research/v8-no-work-100-20260907`. That preceding goal turn made verified
progress and was committed/pushed; this turn consumes its proofs unchanged.
The research worktree started clean. Concurrent main advanced to
`d851f36bc0ee41459156e125aaa04e4a0941ac70`; its unrelated work was not modified
or imported. The final read-only check observed main at
`9b84a1e27d2159ca21fc4ed9dad21b5a9e87daf1`, with its unrelated untracked
V7 CU result directory preserved. No production, verifier, protocol or
performance changes.

## What changed

Three previously missing connections are now kernel-checked:

1. The repaired shifted ordinary rows, affine correction, image augmentation,
   first compact response, adaptive final, ordered queries and compact tail
   form one causal **constructed field game**. Its discrepancy identities
   come from the constructed functional, not correspondence premises supplied
   by an abstract game provider.
2. A sufficiently supported C1 tuple identifies the **original** `earlyC1`
   optional object. Restricting a qualifying width29 tuple then proves its
   first 26 columns are independent of arbitrary late C2/tuple choices.
   No candidate is substituted for `none`, and no efficient decoder is inferred.
3. In the maintained field/hash model, selected path/copy/two-round residuals
   construct the decoder's 24-level path, from trace row59 to row907, without
   an assumed round chain or correct root.

The new proofs remove real interfaces and causality gaps. They do **not**
establish accepted arbitrary-oracle coverage, full payment knowledge, a
complete Rust-to-Lean refinement, resource-bounded Fiat–Shamir or full-view ZK.
The 100-bit global certificate remains absent.

## One causal construction, not retrospective target fixing

The new chain is

```
fixed C1/C2/quotient-prefix analysis data, Q and support
    -> four original functionals + claims, reconstruction L and interpolant I
    -> kappa
    -> affine-corrected shifted ordinary scalar/covector
    -> tau and carried image terms
    -> six-field response0
    -> alpha0
    -> final256
    -> ordered distinct q queries
    -> rho and shifted query injection
    -> three sequential compact responses/challenges
    -> actual field scalar/dot terminal equality.
```

The first line is an explicit **fixing/support hypothesis**, not a statement
that an arbitrary accepted proof has supplied those analysis objects. It may
be after gamma/OOD but must precede kappa for the shifted-row theorem.
Neither a final selected after alpha0 nor a candidate found by a later
extractor is moved backwards through that boundary.

[FirstImageDiscrepancy](first-image-discrepancy-review.md) has a `Before`
record with no tau, response0, alpha0, final or queries. Its image discrepancy
is derived as

```
prior - tau*Q[1023] - tau^2*(b*Q[1022]-c*Q[1021]).
```

Its first discrepancy is the actual compact polynomial minus the actual
honest convolution. The omitted quartic, degree-six boundary and evaluated
folded-dot discrepancy are inherited from the checked V7-consumed grammar.

[CausalOrderedRelation](experiments/CausalOrderedRelation.lean) then enforces
causality through `Strategy`: `firstResponse : K -> Sent K` knows tau but not
alpha0; `final : K -> K -> (Fin 256 -> K)` knows tau/alpha0 but not queries;
the raw tail knows the ordered schedule and rho and reveals each subsequent
challenge only after the corresponding response. Averaging holds this entire
strategy fixed, so a function cannot gain a future sampled challenge through
an unstated argument. This is an ideal conditional law, not a ROM theorem.

Its `accepts` predicate runs the actual modeled compact tail and terminal
scalar/dot comparison; no acceptance Boolean is supplied by the adversary.
Wrong challenge-list lengths reject. The reference Q is an analysis input,
not a witness vector read by that acceptance path: operational post-weights
use ordinary/image weights, and the carried scalar uses the claim/response.
The reference is needed to prove their discrepancies, not to compute the
modeled verifier equality. This remains a field grammar, not a translated
parser or structured SBF accumulator.

### Quotient and fold support are transported explicitly

The actual received slots can be non-polynomial. `fromReconstruction` proves
the V8-specific equivalence

```
(received-I)/L = Q_value  iff  received = L*Q_value+I,  when L != 0.
```

It constructs virtual-quotient agreement from received batched-word agreement
with the reconstruction outside the supplied corrupt-fibre set B. It does
not replace this with V7 raw-word consistency or infer original component
membership from one batched polynomial.

`FixedOracle.folded_support` then uses the actual four-slot order and
normalized fold to derive agreement with the reference final outside B.
The received four slots, x/y coordinates and B are fixed before tau; the
folded received function may depend on alpha0, but not on the later queries.
Nonzero fold coordinates, nonzero chord denominators and the coordinate
mapping remain explicit. Applying the generic construction to every actual
authenticated source opening/encoder remains a separate refinement task.

In particular, the coefficient-space `Rows.reconstruction` and the slotwise
chord denominators are not related merely because both are called L. The
concrete encoder must prove that evaluating the coefficient reconstruction
equals chord multiplication plus the interpolant at each actual slot. That
remaining deterministic bridge, including original-code image membership,
is not a newly assumed root-bound error or a completed authentication link.

### The ordinary rows include the actual affine correction

[ShiftedRowPrefix](shifted-row-prefix-review.md) constructs a covector for
the composition of the original linear functional with L by evaluating it
on canonical coordinate vectors. Its dot identity is proved generically;
no transpose-equality premise is supplied. Its scalar subtracts that same
original functional applied to I.

Therefore the incoming ordinary discrepancy is exactly the polynomial in
four actual original-row errors with powers `[1,kappa,kappa^2,kappa^3]`.
This includes the inactive error at power zero; `inactiveExact` is not a
hypothesis. A nonzero error vector gives a nonzero degree-at-most-three
polynomial. The deterministic unshifted cancellation is not restored.

[CausalShiftedRows.wrong_rows_bound](experiments/CausalShiftedRows.lean)
composes this constructed prefix with the whole causal execution above.
All functionals/scalars, Q, L/I and the received oracle are fixed before
kappa; the later strategy may depend on kappa. The reference's image
validity is a mathematical property, **not** conditioning on a successful
image challenge. Its discrepancy is then constant in tau, uniformly over
every tau, so there is no artificial tau cancellation charge.

## Exactly which bounds now have this constructor

Set `k=(2^31-1)^4`, `T=262144`, `q=22`, final degree cap255. Exact rational
values and current-source evidence are in [causal-row-evidence.json](causal-row-evidence.json).

| Constructed event and scope | Ideal bound |
|---|---|
| Fixed supported reference has wrong ordinary scalar or invalid image | `(q+2)/(k-1)+24/k+choose(|B|+255,q)/choose(T,q)` |
| Same event with exact polynomial received quotient, B empty | `24/(k-1)+24/k+choose(255,22)/choose(T,22)`, approximately118.415037 bits; reuse of the existing restricted result, now through constructed inputs |
| Fixed image-valid reference, at least one wrong original row, full shifted game | `(q+3)/(k-1)+24/k+choose(|B|+255,q)/choose(T,q)` |
| Accepted final differs from the reference fold, including otherwise correct anchors | `q/(k-1)+18/k+choose(|B|+255,q)/choose(T,q)` for that guarded acceptance mass |

At B=9301, the shifted game's bound is
`25/(k-1)+24/k+choose(9556,22)/choose(262144,22)`, approximately
**105.1452753728 bits**. This is the already known row ceiling applied to
a constructed causal execution, not a new global numerical improvement.
The four relation repairs contribute `6/k+18/k=24/k` once. The generic rho
batch still costs q/(k-1), not q-1. The table's events overlap and must not
be added indiscriminately.

The earlier near-gamma ceiling differs by `28/(k-1)`. That arithmetic
relationship does not complete the concrete near-gamma/source composition.
No 100-target union, 396430 aggregate inventory, work multiplier or tiny
invented source/primitive error is introduced. Full probabilities are summed
before display bits; the machine ledger keeps the exact fractions.

These are classical **raw ideal-game** statements. Actual nonce choice,
retries, bounded sampler exhaustion, prequeries, forks/restorations and
extractor runtime still need a resource-bounded non-interactive analysis.
Neither ideal nor resource-bounded security means immunity to unlimited
offline search. No quantum security level is claimed here.

## The early-C1 specialization is genuinely closed

[EarlyC1Specialization](early-c1-specialization-notes.md) resolves the
previous resource failure without changing the early object or its support
premise. Fully explicit types revealed two different `Fintype` instances
for `Fin 262144`: the inherited simplex-derived instance in the source
object versus canonical `Fin.fintype` in the arithmetic lemma. Ordinary
pretty-printing hid the difference, and elaboration tried to reconcile
concrete enumerations.

A generic abstract-carrier cardinality transport is proved first. Explicit
instance arguments and an inferred intermediate proof type then apply the
existing numerical margin without unfolding either enumeration. The exact
optional identification passes with a **lowered** recursion/heartbeat cap.
No replacement option, `some` assumption or assumed candidate membership is
introduced.

`EarlyC1LateProjection` constructs the received width29 word from fixed26
C1 lanes and arbitrary3 C2 lanes. It uses the actual C1 lane indices and
four-slot encoder map. Own support of at least245609 fibres restricts to
C1 support and identifies `earlyC1 c1`; two arbitrary late C2/tuple choices
therefore have equal C1 projections. If the option is `none`, no such
qualifying tuple exists—`none` is not discarded from the security experiment.

This proves mathematical identification/causal independence **given a fixed
received C1 word and qualifying own support**. A fixed Merkle root alone
does not hand an extractor that word. Coupling authenticated/replayed
openings to a fixed word, obtaining it within resources, showing a qualifying
tuple exists, and instantiating early lambda/chi semantic root counts remain
separate tasks. In particular, a later totalization of only observed openings
cannot simply be asserted to have been fixed before lambda/chi.

## The selected path advances the payment endpoint

[SelectedForestPath](selected-forest-path-review.md) connects the decoder's
actual 24 direction/sibling rows to pair/lane blocks4..24 and forest
blocks54..56. It derives ordered children and input-tweak restoration from
selected Boolean/copy/schedule equations. Individual two-round residuals
construct intermediate states and `RoundChain`; the V7 gated-node and
existing generic fold induction then yield the trace endpoint row907 from
the input-note digest at row59. No assumed root or honestly generated table
is needed.

The new `PathResiduals.pairs` predicate uses the maintained mathematical
`gateStep(rc)`. Equality with literal Rust `evaluate_trace_round_pair`, its
constants, lazy-M31 kernels and selected packed evaluator is **not** claimed
translated. The public-binding residual at row907 is present in source,
but this theorem does not silently take the independently authenticated
caller root from prover data. Owner/key/note/nullifier realization, amount
positivity, output/append transition and authoritative runtime/settlement
validation remain to compose. This is a modeled deterministic prerequisite,
not a complete returned-payment-witness theorem.

## Accepted extraction accounting after this continuation

The target remains A AND NOT X: complete repaired-verifier acceptance and
failure of the specified bounded extractor to return a checked payment
witness. The prior [total-accounting template](ordered-post-query-review.md)
still applies; its bookkeeping is not mistaken for a proved source partition.

| Remaining stage | What this turn changes | What remains unbounded/unproved |
|---|---|---|
| Authenticated access/replay | Nothing silently assumed from a root | Fixed-word coupling, canonical graph/decoder access, abort/fuel/missing responses/challenge mismatch and provider-none |
| Near support and early C1 | Exact optional identification and late-C2 projection now checked | Acceptance produces a qualifying tuple; concrete near-gamma/source composition and bounded decoder |
| Supported bad relation/image execution | Constructed causal rows/image/ordered-query grammar has the stated bound | Concrete chord/selector/parser/optimized-source instantiation; no-anchor/far accepted recovery |
| Correctly bound tuple to individual constraints | Early mathematical projection is now available | Earlier lambda/chi challenge argument from authenticated fixed C1; correct point claims alone are insufficient |
| Coefficients/constraints to payment | Pair/direction and modeled24-step path now checked | Literal field/hash/source, owner/note/nullifier, full public/context/output/settlement endpoint |
| Non-interactive/privacy | No change to messages or witness footprint | FS resources and adaptive full-view simulator remain separate |

Rows can be made disjoint by precedence for bookkeeping, but later replay
or decoder outcomes may not be conditioned on to preserve a fresh-query
law. Bounds must dominate their relevant events in a constructed coupled
experiment. Deterministic correspondence is not assigned a probability.
The numerical global allowance stays null.

Original/paired root-product counterexamples remain visible in the far
regimes; high-J uses its own support, not the disproved same support. T512
uses the image-aware game, not query-only suppression. The zero-fold image
kernel, shifted/late-inactive/rho/later-repair cases retain their scopes.
An honest out-of-radius execution with correct rows and the true final is
not covered by a *wrong-row* event and can still extract successfully. Radius
failure is not relabelled extraction failure. Unchanged regressions were not
replayed.

## Focused evidence and unchanged cost

All claimed leaves use only standard axioms (`propext`, `Classical.choice`,
`Quot.sound`, or none). No retained `sorry` or new axioms. Logs include exact
source/import/olean pins, exit status, wall time, RSS and swap. The runners
reuse the pinned Lean4.32.0/Mathlib81a5d257 cache, serialize jobs, resolve the
Lake environment first, use `-M7000`, and independently stop aggregate
descendants at7GiB. They do not launch a cold dependency build or modify main.

| Final leaf | Exit | Wall seconds | Peak RSS bytes | Swaps |
|---|---:|---:|---:|---:|
| FirstImageDiscrepancy | 0 | 3.60 | 5,664,161,792 | 0 |
| CausalOrderedRelation | 0 | 4.94 | 5,687,312,384 | 0 |
| ShiftedRowPrefix | 0 | 11.84 | 5,654,691,840 | 0 |
| CausalShiftedRows | 0 | 3.46 | 5,660,229,632 | 0 |
| SelectedForestPath | 0 | 3.31 | 5,651,824,640 | 0 |
| EarlyC1InstanceTransport | 0 | 0.72 | 1,282,588,672 | 0 |
| EarlyC1Specialization | 0 | 3.23 | 5,647,155,200 | 0 |
| EarlyC1LateProjection | 0 | 3.93 | 5,656,756,224 | 0 |

Missing ClaimTransport and V7 gated-Merkle importable artifacts were exported
once. C1's two new guard failures and low-limit diagnostics remain in its
report; the solution changed symbolic interfaces, not caps. The causal leaf's
first run failed on Lean's reserved `prefix` identifier, then passed after
renaming it `atFold`; the dependent shifted game passed on its first run.
Other local namespace/row-normalization/cache-root/noncomputable-keyword
errors and their repairs are preserved in the linked focused logs. Warnings
about unused section variables or a redundant tactic combinator do not
weaken a theorem and did not trigger unchanged reruns.

From the research worktree, use fresh log names and the documented existing
caches; compile only changed targets:

```sh
bash docs/research/v8-no-work-100-20260907/experiments/run_causal_ordered_relation.sh /absolute/NEW-causal.log
bash docs/research/v8-no-work-100-20260907/experiments/run_causal_shifted_rows.sh /absolute/NEW-shifted.log
python3 docs/research/v8-no-work-100-20260907/experiments/audit_causal_rows.py --check-recorded
```

The other runners and cache/export order are linked from the subreports.
The machine audit counts axiom-free audits as well as standard-axiom ones
and verifies final current-source hashes against successful logs. No new
Rust/SBF, proving-time, extractor-runtime or CU measurements were performed.
The body remains `697*16+52+24+22*621+2*296*26 = 40,282` bytes, with zero
new messages or verifier operations. Prior worst observed complete CU remains
1,047,041, not a universal accepted-input CU certificate.

## Next decision

Keep QM31 q22 as the primary profile. The conditional field execution is
now sufficiently constructed to make the next recovery work concrete:
couple the authenticated fixed C1 word and the near-gamma own-support tuple
to this early-C1 projection and the actual individual semantic/copy checks.
The single next focused experiment should construct that fixed-word/source
coupling for the current bounded extractor, explicitly retaining missing
openings, replay/fuel failures and far regimes. If its word is selected only
after semantic challenges, that is a precise causality obstruction to fix,
not something the new optional-object theorem permits us to assume away.

This does not replace the genuinely new mathematics still needed for
accepted uncovered recovery. Production confidence requires that global
argument and all source/payment/FS/privacy gates, not more display bits from
the now-connected conditional row game.
