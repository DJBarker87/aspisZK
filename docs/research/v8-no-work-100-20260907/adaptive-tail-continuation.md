# Adaptive off-family finals: two agreement tails, one query bound

Research parent: `b006d34ffc6d552cd5ecd9f292cf2bd095f7fdb9`.
Branch: `research/v8-no-work-100-20260907`.
Borrowed V7 source: `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.

## Result and scope

The new route bounds a previously unbounded class: the actual alpha-adaptive
final is not the fold of any quotient polynomial agreeing with the fixed
received quotient on at least 9,558 complete fibres. It does not assume
that the received quotient is a polynomial, or that a provider returns a
candidate. The construction uses the selected circle encoder, not V7's
original-word consistency event.

**Replay status:** both selected agreement tails and their actual indexed-query
and compact-suffix composition are Lean-checked. `SelectedOutsideQuery` derives
the field-domain matching-set correspondence; no missing source equality is
supplied as a premise in that mathematical endpoint. The fixed-C1 wrapper and
its explicit remaining-event partition also passed. This is a source-shaped ideal game, not a translated
Rust verifier or an actual Fiat–Shamir execution.

For full-field fresh alpha and fresh distinct q22 queries the pointwise ceiling
is approximately `2^-104.5921337294`. With the source-shaped shifted rho batch
and three later compact relation rounds it is approximately
`2^-104.5920507688`. These are **off-family event bounds**, not complete V8
soundness, payment knowledge, an efficient extractor, or a Fiat–Shamir theorem.
No verifier, proof profile or public message changes are needed for this
mathematical result.

## Actual objects and fixing boundaries

Fix any legal prefix determining an arbitrary received quotient
`R : Fin 1048576 -> QM31`. In the component execution R is derived from early
C1, adaptive C2, both sequential OOD vectors, gamma and the chord. It is not
chosen after the first folding challenge. Ordinary rows and scalar are fixed
before kappa/tau as in the corrected callback; response0 knows tau, not alpha.

Define a mathematical family, using only this R and the selected domain:

```
F = { Q : Fin 1024 -> QM31 |
      at least 9558 complete fibres have exactInitialEncoder(Q) = R
      on every one of their four slots }.
```

F is fixed before alpha (indeed before kappa/tau once R is fixed). Its
members need not have a valid reconstruction image, correct ordinary rows,
or component-wise payment meaning. No efficient enumeration is asserted.

The actual final `F_alpha : Fin 256 -> QM31` may depend on tau and alpha. Let
M be the size of the **full actual** equality set between its selected final
evaluation and the canonical four-slot fold of R. `Outside` means that no
Q in F has `F_alpha = coefficientFoldLayer 256 alpha Q`.
Both M and Outside are fixed before the fresh queries. Neither is the generic
provider's `none` event. Query residuals keep their actual signs and order;
rho comes after the schedule, and later compact responses are sequential.

## Why the two tail bounds are new information

### Moderate agreement: reuse the old theorem on a masked strategy

The pinned V7 degree-three curve theorem already supplies the exception
numerator `C = 9,396,508,281,246` at agreement threshold 9,557. Its original
conclusion is a coherent selected subfamily, not coverage of every adaptive
final. Merely quoting that conclusion would leave the same gap as before.

`MaskedCurveTail` instead empties the strategy's support on represented
branches, leaving its actual candidate unchanged. Apply the old theorem to
this masked strategy. If more than C remaining alpha values have at least
9,558 matches, the theorem constructs four code-valued lanes and a resolving
selected alpha. That node's support is contained in the constructed tuple's
own support. Consequently the tuple belongs to the fixed family and represents
that node's actual final, contradicting its retained Outside condition.

Thus the number of actual Outside alphas with M at least 9,558 is at most C.
This is a genuine mask-on-the-uncovered-event argument, not a membership
premise or assumed successful provider. The source-shaped adapter proves
decoded-lane support equals literal raw four-slot support and that the
interleaved coefficient fold is the selected candidate curve.

### High agreement: four intersections force representation

Any four Outside alphas have fewer than 9,558 common matching fibres.
Otherwise four-fold interpolation constructs Q on that common support.
Because 9,558 exceeds the final code's 255-point overlap cap, each of the
four actual finals equals the corresponding fold of Q. Q is in the family,
contradicting Outside. No target is retrospectively fixed before alpha.

Now suppose 128 Outside alphas each have at least 117,965 matching fibres.
Double count incidences of four supports and apply the proved discrete
binomial tangent inequality to the fibre loads. The exact certificate is

```
floor(128*117965/262144) = 57
262144*choose(57,4)/choose(128,4)
  = 30818304/3175 > 9557.
```

Some four supports must therefore have at least 9,558 common fibres, a
contradiction. There are at most **127** such high-agreement Outside alphas.
This supplies information about the unknown agreement distribution, rather
than just reproving its query-last expectation identity.

## Exact query and compact-relation composition

Write `b(m) = choose(m,22)/choose(262144,22)` and `k = (2^31-1)^4`.
Partition actual Outside branches by M. Conditional query probabilities are
monotone in M, so summing the three masses gives

```
M <= 9557:             b(9557)
9558 <= M <= 117964:   (9396508281246/k) * b(117964)
117965 <= M:           127/k

epsilon_out_pointwise = their sum.
epsilon_out_suffix = epsilon_out_pointwise + 22/(k-1) + 18/k.
```

The two tail counts are charged against the same actual adaptive final
strategy. There is **no family-size multiplier on b(9557)**. The generic
`TwoTailQueryBound` proof keeps the Outside indicator and sums probabilities
before converting them to bits. `SelectedOutsideQuery` derives the matching
set's field-domain/indexed bijection, then consumes the actual compact suffix
theorem. A nonzero incoming prior or query residual is not discarded.

The suffix bound counts rho and the three later degree-six relation repairs
once. It does not require a first-round root bound: for this class even an
arbitrary zero prior is upper-bounded by the pointwise matching mass. Adding
the image/row/near ceilings wholesale would double count suffix events.

The exact rational ledger is `adaptive-tail-budget.json`; unsupported global
terms and the remaining global allowance remain null. The historical 396430
inventory is not imported. Privacy is not assigned a soundness probability.

### Checked dependency map

| Leaf | Mathematical result / actual interface |
| --- | --- |
| `MaskedCurveTail` | Mask out covered responses before consuming the pinned V7 degree-three theorem; bound uncovered alpha count |
| `MaskedCurveRepresentation` | Decoded four-lane curve, interleaved coefficients and whole-fibre support are the same objects |
| `SelectedMaskedCurveTail` | Instantiate that masked bound for arbitrary selected received slots; moderate tail is at most 9,396,508,281,246 |
| `HighAgreementTail` | Symbolic binomial tangent and exact 128-support/four-intersection certificate |
| `SelectedSupportIdentification` | Four common supports reconstruct a selected quotient and identify the actual final by the 255-point overlap bound |
| `OffFamilyIntersection` | Selected off-family high-agreement tail is at most 127 alphas |
| `TwoTailQueryBound` | Sum low/middle/high actual query masses, not family-wise query bounds |
| `SelectedOutsideQuery` | Selected indexed/field-domain matching equality and the actual causal compact suffix bound |
| `FixedC1OutsideQuery` | Apply that bound to the actual fixed-C1/helper execution, average gamma/kappa, and retain the covered far/wrong-C1 remainder |
| `FoldSupportClosure` | Reused collector control: four matching folds determine all four slots; observed closure does not create a stronger full-support intersection |

The old curve-decoding result is reused at its pinned hypotheses. Its large
exception numerator is multiplied by the independently justified middle-region
query probability; it is not relabelled as a stronger unweighted recovery
error. The high-region cap supplies the essential extra information where that
query probability would otherwise approach one.

## What remains in accepted extraction failure

The next partition is an obligation map, not an assertion that the full
Rust/Fiat–Shamir execution is already coupled to the ideal game:

| Actual class | Current treatment |
| --- | --- |
| Scalar acceptance with nonzero prior or nonzero pointwise residual | Actual degree-q rho and later relation repairs; charged once in joint composition |
| Actual final outside the fixed quotient family | New two-tail pointwise and compact-suffix bound |
| Represented Q with invalid image or incorrect ordinary rows | Must use the carried image gate and shifted row mixing jointly against the prechallenge family; finite-family/source wrapper still needed |
| Represented, image-valid and correct-row Q but wrong component/OOD claims | Fixed-early-C1 degree-two helper and degree-28 error remain; no global far-gamma recovery bound yet |
| Correctly recovered C1 but failed payment/context/settlement witness check | Existing deterministic prerequisites, with accepted semantic/copy/path enforcement and bounded endpoint still to connect |
| Authentication, replay abort/fuel, missing responses, cached/advance mismatch, provider-none | Remain actual extractor/source obligations, not replaced by Outside |

An optional family-cardinality audit gives a route through the existing
Johnson machinery with cap 99 (and a separate unformalized cap-92 refinement).
Those factors belong on **covered bad-image/row collision events**, not on
the actual off-family query mass. See `quotient-family-audit.md`. This turn
does not promote its proposed covered-family composition to a checked theorem.

The family is fixed after gamma, not before it. The fixed early C1 source
boundary, degree-two helper curve and degree-28 claim error must remain
visible when treating the covered gamma/component branch. This result does
not license moving a Q extracted after C2 or gamma backwards to lambda/chi.

The checked fixed-C1 wrapper consumes the existing `Execution` interface, including
its explicit successful early-C1 identification. It does not prove that
identification exists for every accepting proof. Its proved endpoint is
`farProbability <= epsilon_out_suffix + coveredFarProbability`, with the
covered term still actual compact acceptance, not an assumed witness. The
standalone arbitrary-R theorem does not need the early-C1 premise; absent,
sparse and failed early-C1 recovery paths remain in the global extractor map.

## Permanent regressions and bounded collector experiment

| Regression | Treatment under this partition |
| --- | --- |
| Original/paired root products | Family membership is tested for the actual gamma-dependent quotient, not assumed from an original component tuple; covered gammas still need component recovery |
| High-J own-support construction | May be represented without same-support component recovery; the covered-component obligation remains |
| T512 exact invalid image | Fully represented in the full-Q family; handled by image/relation reasoning, not this Outside theorem |
| Zero-fold/nonzero-image kernel | Final-only membership still cannot replace carried image checks |
| Unshifted/late-inactive and shifted-query cancellations | Repairs and causal order unchanged; legitimate rare roots remain allowed |
| Radius-boundary valid witness | Being far from an arbitrary radius cutoff is not extraction failure |

The separate overlap collector control found that partial observed supports
can grow through fourfold closure, but actual full matching sets do not gain
extra geometry that way: for coherent finals, fourfold multiplicity recovers
exactly the quotient's whole-slot support. It does not fix the earlier lack
of a coherent seven-alpha group. This negative finding motivated the direct
adaptive-family tail proof above. See `fork-overlap-review.md` and
`fold-support-closure-review.md`; no old exhaustive strategy search was rerun.

## Execution and cost

Initial focused leaves ran on the laptop under the user's laptop instruction.
After the user requested a return to the NUC, no new laptop Lean jobs were
started. The already-running small selected check was allowed to finish;
remaining checks use an isolated NUC overlay, pinned imported artifacts and
serial memory-capped systemd scopes. No unrelated NUC services are changed.
Exact commands, source/olean hashes, exits, time, RSS, swap and axiom audits
are retained with the focused logs and evidence manifest.

| Successful focused target | Host | Wall seconds | Peak RSS bytes |
| --- | --- | ---: | ---: |
| FoldSupportClosure v2 | laptop, before move | 30.02 | 5,524,455,424 |
| HighAgreementTail v3 | laptop, before move | 12.79 | 2,848,374,784 |
| MaskedCurveTail v1 | laptop, before move | 59.81 | 4,496,375,808 |
| MaskedCurveRepresentation v1 | NUC | 3.07 | 6,847,401,984 |
| SelectedSupportIdentification v2 | NUC | 3.28 | 6,988,402,688 |
| OffFamilyIntersection v2 | NUC | 3.10 | 6,990,970,880 |
| TwoTailQueryBound v4 | NUC | 1.82 | 3,373,621,248 |
| SelectedMaskedCurveTail v7 | NUC | 3.91 | 7,009,435,648 |
| SelectedOutsideQuery v3 | NUC | 3.25 | 7,026,581,504 |
| FixedC1OutsideQuery v2 | NUC | 3.27 | 7,033,036,800 |

Every successful leaf exited zero with zero recorded swaps and only the
standard Lean axioms `propext`, `Classical.choice`, `Quot.sound` where used.
No retained theorem contains `sorry` or a new axiom. Failed checks' generated
`sorryAx` diagnostics are explicitly not successful evidence. New arithmetic
and collector controls are separately host-tested, not cryptographic
probability experiments: the exact arithmetic check took 0.41 seconds/
17,727,488 bytes RSS; the optimized collector took 0.41 seconds/1,982,464 bytes
RSS after 1.27 seconds/175,276,032 bytes of compilation.

The remaining NUC runs used one serial scope with `MemoryHigh=8G`,
`MemoryMax=10G`, `MemorySwapMax=0`, `CPUQuota=200%` and Lean `-j1 -M9500`.
Earlier 7-GiB-scope failures occurred while importing the cached native
dependencies, before the mathematical targets. The affected generic query
leaf and geometric selected leaves had their imports narrowed before another
check; an unchanged failed target was not rerun with a larger cap. The generic
query leaf then used about 3.37 GB RSS. Concrete `Fin 262144` instance mismatches
were repaired by symbolic cardinality transport and target-directed rewriting,
not by raising recursion limits or reducing its enumeration. Failed attempts
and their exact source versions are retained alongside the successful checks.

Reproduction uses the pinned cache and isolated overlay documented in
`masked-curve-tail-review.md`. The focused selected endpoints were run with:

```sh
bash run_masked_nuc_selected.sh /home/dombarker/project-offloads/aspis-masked-tail.SH0QtS SelectedOutsideQuery selected-outside-query-nuc-v3
bash run_masked_nuc_selected.sh /home/dombarker/project-offloads/aspis-masked-tail.SH0QtS FixedC1OutsideQuery fixed-c1-outside-query-nuc-v2
```

The runner refuses to overwrite an existing evidence tag. A genuine new replay
needs a new tag and a stated source/environment/evidence reason. The final
read-only audit is
`python3 -B experiments/audit_off_family_tail_evidence.py --check-recorded`;
it verifies current-source hashes, imported artifact
provenance, resources and standard-only axiom logs without rebuilding anything.
Native package compilation is a pinned trusted-cache boundary, not a claim
that all of Mathlib was rebuilt or translated in this continuation.

Final read-only `--check-recorded` audit passed with exit 0: all ten current
leaves, their 51 named standard-only axiom audits, exact arithmetic and the
collector control match the retained evidence. The receipt includes all 23
NUC attempts and 55 transferred artifact versions; 21 failed diagnostics
(including the earlier laptop checks) are preserved rather than silently
discarded. Python syntax checks and each shell runner's syntax check passed.
The staged whitespace audit reports one retained final blank line in the
already-hashed `run_masked_nuc_selected.sh`; its executed bytes are preserved.
There are no other whitespace findings. No unchanged full Lean/Rust regression ran.

The body remains exactly

```
697*16 + 52 + 24 + 22*621 + 2*296*26 = 40,282 bytes.
```

There are no added verifier operations or public messages. This is not a new
prover/RSS benchmark, SBF measurement or full-transaction CU result. NUC formal
checking time is not prover/extractor time. No production changes, activation,
deployment or main-branch edits are made. Full-view simulation and the
resource-bounded Fiat–Shamir lift remain separate, with prequeries, retries,
nonces, restorations, forks and fuel explicit; grinding has zero positive credit.

## Decision

QM31 q22 still deserves priority. A promising missing arbitrary-oracle class
now has a direct adaptive-tail route with a margin above 100 bits, without
changing field, queries, domain or proof body. That does not finish extraction:
the decisive next mathematical task is the **covered quotient-to-component
step across gamma**, retaining the fixed early C1, quadratic helper curve and
degree-28 claim discrepancy. It must either construct a legitimate early
component representation or bound the actual accepted uncovered mass; an
assumed tuple member or an uncharged family union is not enough.

The next bounded experiment should apply the analogous masked-family/support
intersection analysis to the three helper lanes, preserving the genuine
ordinary/image constraints and OOD timing. It should test any proposed tail
against the original/paired/high-J constructions before formalizing it. It
must also test mixed-support C1 words: disagreement with one chosen early
decoder output is not automatically absence of another valid payment witness.
A failed proposed `wrongC1` bound must not be promoted to a knowledge attack;
the extractor may need a causally fixed family and an alternative checked
witness. The current theorem deliberately leaves that represented remainder
visible.
