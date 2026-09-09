# Helper-curve reduction and concrete payment/query interfaces

Continuation base: `1b8f72d9de123b16eb831754e58518e66a33d3f3`, on
`research/v8-no-work-100-20260907`. The previous status turn made no source
change; this continuation resumes the pending proofs and executes a new
causal strategy experiment. Borrowed formal sources remain pinned to
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`. Concurrent main was observed at
`e674314c6d062377f29df84f3c4c94d4ebd7572d`; its candidate-directed V7 work and
testnet results were not changed.

## What this continuation changes

The new work advances three different edges of the intended extraction
argument. None assumes that recovered coefficients are already a valid
payment, and none changes a verifier acceptance condition.

| Edge | New result | Boundary still explicit |
|---|---|---|
| Selected C1 amount cells to decoded transfer amounts | Same-table positivity pack, literal copy links, source range reconstruction and conservation imply positive canonical amounts,30-bit bounds,natural conservation and safe u32 addition | Acceptance must enforce the individual residuals; this is not the whole owner/path/context/settlement witness |
| Derived chord/query data to checked inverses | Actual five-coefficient preparation, canonical half, ordered line/norm buffers and one shared inverse with backward updates equal the checked field/list model | Actual selected-point lookup, parser, mutable Vec and machine arithmetic translation |
| Fixed C1 support to remaining unknown helper curve | Literal26+3 affine normalization reduces the unknown received curve on that support to H+gamma G+gamma²D; the actual early-C1 object now supplies a constructed helper-message cover | Does not remove false C1 claims, charge the remaining accepted mass or supply an efficient helper extractor |

Detailed source maps and proof hypotheses are in
[the amount endpoint](selected-amount-endpoint-review.md),
[the norm-buffer bridge](line-norm-buffer-review.md), and
[the C1/helper analysis](fixed-c1-helper-review.md).

### The payment implication is genuinely deterministic

The new endpoint starts with an arbitrary base-field C1 table. It derives
the helper-to-decoder amount equalities through the seven literal selected
copy records, rather than receiving those equalities as independent inputs.
The source's reverse-Horner ten-bit reconstruction is proved equal to the
weighted sum used by the reused V7 range theorem. The compiled Boolean and
conservation sign conventions are handled algebraically, and all six actual
auxiliary-zero equations remain in the stated source predicate. No host
zero-padding class is deleted to make a fixture pass.

The source-shaped sparse current/successor reads come from this **same**
lifted table. The product-inverse pack then implies strictly positive output
amounts. The seven copy links transport that fact to decoded rows460/508;
conservation also establishes a positive input at row44. This supplies the
transfer compiler's strict amount requirement without assuming decoder
success, a valid witness, or an honest trace. It applies to the opt-in
positive-transfer **research** repair, not to production by inference.

### The query implementation no longer assumes its own buffers

`SharedInverseReplay` models one inversion of the two total products,
the two derived seeds and the actual reverse updates. It proves equality
to the checked separate/joined specifications, including rejection.
`LineNormBuffer` constructs the CM31 coefficients and the ordered line
coordinates from the same typed circle points. It proves the produced norms
are the norms of the actual four signed chord denominators, derives their
scalar norms, and consumes the constructed norms during inverse rebuilding.
The final equality can be used with the preceding `QueriedResidual` results;
reciprocal or buffer correctness is not supplied as a new premise.

Typed circle points still carry their defining invariant. Constructing those
points from the actual selected index/parser path, and translating mutable
machine execution, are subsequent deterministic obligations—not small
probabilities assigned to the toolchain.

### The new cover is connected to the actual early-C1 object

`ThreeHelperCover.cover_dichotomy` proves the generic quadratic case:
on a fixed support D with distinct-codeword overlap at most delta, if
`4B+delta<|D|`, either fewer than three good gamma values exist, or one
constructed three-coefficient code tuple covers **every** B-close candidate.
It constructs the nodal codewords and their common support from the fixed
received curve; no provider or assumed family membership supplies the tuple.
The candidate may be selected after gamma.

`ThreeHelperSelected.early_cover` now instantiates the substantive source
interfaces. Given the unchanged `earlyC1 received=some p`, it derives the
actual componentwise own support S with at least245,609 complete fibres.
It uses the selected original encoder, actual four-slot fibre map, proved
code overlap and encoder injectivity. For arbitrary fixed received C2:

```
fewer than3 Good gammas
 OR there exist3 pre-gamma helper messages h such that every original-code U
    with at most61,338 raw bad fibres ON S satisfies
      U = sum_{j<26} gamma^j p_j
            + gamma^26 * sum_{j<3} gamma^j h_j.
```

The strict numerical margin is `4*61338+256=245608<245609`.
Good is defined from the actual helper curve, S and original-code proximity,
not from provider success or the sampled final. The proof shows the raw and
normalized-helper bad-fibre sets are identical on S, then reconstructs
**message coefficients**, not just matching evaluations. It asserts
nothing about excluded C1 fibres and keeps the sparse alternative. All26 C1
lanes are represented by the early object; correctness of just the16
semantic lanes is not substituted for that premise.

This is a genuine broader coverage statement, but still not an accepted
execution probability theorem. An image-valid reconstructed quotient must
be connected to the raw candidate U under the real image/row game. The
arithmetic `4*15334+2=61338` identifies a possible enlarged final-distance
region using the earlier geometric/pole estimates; **that new game
composition is not claimed here**. The helper tuple exists mathematically;
no efficient algorithm finding it from the actual replay interface is
established. The claim discrepancy retains its full degree28, including
the degree25 C1 error after affine subtraction.

An independent sharp-margin control in `three_helper_cover_checks.py`
constructs four quadratic received coordinates over F7. At four nonzero
gammas they are one-error-close to the constant codewords gamma³, but no
single quadratic code curve covers all four. Here `|D|=4B=4`, so the strict
margin correctly excludes it. Adding every possible fifth quadratic
coordinate exhausts343 restricted received curves: all4 dense cases obey
the cover and339 retain the sparse branch. These finite checks supplement
the universal Lean proof; they are not cryptographic probability estimates.

## New causal strategy test: the final changes the scalar too

The previous `radius_strategy.rs` remains correct evidence for its stated
reduced discrepancy game. It does not include the final's effect on the
carried scalar. The materially different question tested here is what
happens when the post-alpha final choice also changes the prior by

```
delta = response0(alpha) - dot(folded_weight(kappa,tau,alpha), final).
```

`final_transport_strategy.rs` implements exact backward induction in an
explicit F11 reduced linear-code game. It uses eight positions, two distinct
queries and all11^4 four-coefficient finals. The fixed received noise is on
two fibres before alpha. Three product covectors retain shifted ordinary
scales kappa,kappa²,kappa³. The reduced image covectors e15 and e14-2e13
contribute to the last folded weight; the search does not restrict finals
to a subspace annihilating that image weight.

Causal order is gamma, inactive scalar, kappa, tau, response0, alpha,
final, query subset, rho, then three sequential discrepancy rounds. The
inactive scalar may depend on gamma but not kappa. Response0 may depend on
tau but not alpha. The final may depend on alpha but not queries. All later
responses may depend on prior revealed challenges.

The first response is deliberately a **restricted family**: only c0 and c1
are free, c2/c3/c5/c6 are zero, and c4=claim/4-c0. All121 choices are
enumerated. Every final is enumerated. Later degree-six compact discrepancy
responses are unrestricted: a displayed six-root polynomial with nonzero
boundary, scaled to each prior, attains the root bound, so their exact
three-round repair optimum is1206/1331. The query batch is the shifted
degree-two polynomial `delta-rho*(r0+rho*r1)`.

| Fixed-point-claim experiment | Correct final transport | Deliberately omitted transport |
|---|---:|---:|
| Honest point claims, arbitrary permitted inactive scalar | 787371/819896 | 787371/819896 |
| Fixed false C1 row0 claim | **7736389/8198960** | **384763/409948** |
| False row0, also selected final distance>1 | 1100963/1171280 | 95817/102487 |

For the false row, the correct optimum is approximately0.943582 versus
0.938565 in the altered model. Thus dropping the final-dependent scalar
term can **underestimate** adaptive acceptance even in this small fixed
family. This is an obstruction to that simplification, not a payment
forgery. The honest control does not show the difference, so honest-fixture
agreement alone would miss it.

The implementation compares its histogram method with direct scalar
evaluation on3,630 fixed checks. It also verifies that allowing the first
response after alpha, or the inactive scalar after kappa, only increases the
corresponding optimum; those deliberately invalid schedules are separately
labeled and are not used as legal strategies.

This is **not an Aspis circle domain** or a genuine semantic/payment prefix.
The source successor/OOD/chord construction is not modeled here; one
ordinary row is a fixed distinct product functional, and the reduced chord
coefficients are fixed analysis constants. There is no extrapolation of
F11 rates to QM31, no search over arbitrary committed words, and no universal
upper bound on adversarial first responses. The experiment is useful because
it preserves the causal scalar/query interaction that the next universal
argument must handle.

### Reproduction and measurement scope

```
bash docs/research/v8-no-work-100-20260907/experiments/run_final_transport_strategy.sh /tmp/final-transport-recheck.log
```

Use an unused log filename. The recorded run used Apple M3,
`rustc1.93.0`, `-O -C overflow-checks=yes`, a1GiB process-tree RSS guard
and180 CPU-second child limit. Compilation: exit0,0.93s,131,678,208-byte
peak RSS. Strategy execution: exit0,0.73s,5,865,472-byte peak RSS. Both had
zero swaps. The histogram occupies3,543,122 bytes. This timing is for an
exact reduced mathematical search, **not proving, witness extraction or CU**.

## Correct remaining event accounting

The target remains `Pr[actual acceptance AND checked-witness extraction fails]`.
The following precedence must eventually be coupled to actual source and
extractor executions; the table is not itself a proved global partition.

| Class / fixing boundary | What is justified now | What is not assigned a number |
|---|---|---|
| Authenticated fixed C1, before private extractor sample | Existing `earlyC1=some` private coefficient-recovery theorem remains usable under its explicit interfaces | Actual opening/replay access, canonical descent and decoder/source instantiation |
| Correct semantic coefficients recovered | New amount endpoint derives one validator requirement from the exact individual source-shaped constraints | Acceptance-to-those-constraints, remaining ownership/note/path/context and settlement completeness |
| Incorrect ordinary/OOD/semantic claims, especially far finals | C1/helper normalization retains their full scalar-power discrepancy; new causal test retains final transport | Actual accepted false-claim probability |
| `earlyC1=none` and extraction fails | Remains visible regardless of radius or provider return | Its complete accepted mass; `none` is not synonymous with no valid witness |
| Query inverse/source boundary | New constructed field/list equality closes a deterministic interface | Parser/index/machine/authentication refinement, rather than an invented error term |
| Replay abort/fuel/missing response/cached-advance mismatch | Must be retained in the specified resource-bounded extractor | No unsupported negligible bound |
| Any execution yielding a checked valid witness | Zero contribution to failure | No need to force it into an arbitrary radius classifier |

The earlier private-sample decoder event and near-gamma/image/row events are
not automatically added. No new relation-repair probability is charged by
the deterministic amount or inverse proofs; existing repairs must be counted
once under a justified global partition. The historical396430 inventory is
not imported. Global raw error, remaining global allowance and the
resource-bounded Fiat–Shamir bound remain explicitly unset in the ledger.
Private-sampler law, nonce/retry/prequery selection and fork/restoration
resources are still separate from the ideal algebra. Full-view adaptive
privacy is also still a separate requirement.
The requested eventual100-bit claim is classical and must specify its
resource regime; this continuation makes neither a quantum-security claim
nor a claim against unlimited offline search.

The original/paired root products, high-J own-support distinction, T512
invalid-image obstruction, zero-fold image kernel, unshifted-row cancellation,
late-inactive timing falsifier, shifted query/later repairs and harmless
out-of-radius D corruption remain regressions. None was discarded or
rerun unchanged. No new public messages, masks or verifier operations were
introduced by this work.

The maximum body remains exactly

```
697*16 +52 +24 +22*621 +2*296*26 =40,282 bytes.
```

No SBF/full-transaction CU, prover-latency or new privacy measurement is
claimed. The opt-in positive-transfer repair's full-pool cost/privacy gates
remain open. Production and main are unchanged.

## Decision and next boundary

Keep the present profile while the mathematical/source connection advances;
this continuation supplies no reason to enlarge the field, query count or
body, and no reason to declare the global security goal complete.

The next decisive composition is to consume `ThreeHelperSelected.early_cover`
in the actual image/row game, with the full degree-28 claim error and
final-dependent scalar transport. It must identify the remaining far
accepted mass explicitly. The cover is now instantiated on the actual
early-C1 own support; its probability/game connection is the next boundary.
A cover for some anchors is not an acceptance theorem, and a coefficient
decoder is not yet a checked payment-witness extractor.

The current-source proof audit is in
[helper-source-continuation-evidence.json](helper-source-continuation-evidence.json).
All nine retained leaves pass with standard axioms only and zero swaps.
No package-wide Lean/Aeneas or unchanged heavy replay ran.

| Leaf | Final log version | Wall seconds | Peak RSS bytes |
|---|---:|---:|---:|
| SharedInverseReplay | v1 | 11.92 | 2,859,483,136 |
| LineNormBuffer | v3 | 16.08 | 5,606,490,112 |
| SelectedAmountEndpoint | v3 | 15.42 | 5,656,395,776 |
| ScalarPowerSplit | v1 | 1.41 | 1,417,658,368 |
| ScalarPowerSplitInstances | v1 | 1.50 | 1,416,757,248 |
| FiniteSumConcat | v1 | 1.13 | 1,418,100,736 |
| FixedC1HelperReduction | v8 | 21.01 | 5,738,283,008 |
| ThreeHelperCover | v2 | 13.53 | 5,638,488,064 |
| ThreeHelperSelected | v3 | 15.98 | 5,734,105,088 |

The source split initially exposed imported finite-enumeration and
additive-instance conversion costs. Generic symbolic lemmas and a tiny
explicit-type diagnostic isolated them; the successful implementation uses
an additive-monoid-only concatenation adapter. It restores the original
recursion-depth limit and does not increase memory or heartbeat caps.
Failed diagnostic logs are retained separately, never used as successful
proof evidence. Final source/olean hashes, commands, time/RSS/swap and
`#print axioms` outputs are recorded and checked against current files.

```
python3 docs/research/v8-no-work-100-20260907/experiments/audit_helper_source_continuation.py --check-recorded
```
