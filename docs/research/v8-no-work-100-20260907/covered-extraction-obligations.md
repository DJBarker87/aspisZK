# Covered candidates: early C1 families and checked-witness extraction

Read-only continuation audit at
`bc23dfeb647320c4fbf09012cd92da1a6a5fa95a`, research branch
`research/v8-no-work-100-20260907`. The current family and mixed-C1 work is
concurrent and is not counted below as a completed theorem. No Lean, Rust,
NUC, SBF, prover, or arithmetic gate was run for this audit. Production and
all previously frozen evidence remain unchanged.

## Decision

A decoder returning the dominant early C1 tuple is not yet the right
knowledge-extraction endpoint. It may return a tuple that fails payment
validation while a different, less-supported tuple yields a valid witness.
The extractor must count any witness passing the literal selected
payment/context/transition check as success. A mathematical candidate family
and an efficient procedure enumerating its relevant members remain distinct.

V7 supplies useful, genuine causal family machinery. It does **not** already
prove that the repaired selected V8 verifier enforces the payment relation
for all relevant candidates. The next concrete deterministic bridge is the
current **weighted 136-link Copy LogUp-to-alias** implication. Its algebra
can reuse the old proof; its registry, active-link selection, tuple patterns,
and caller-bound append index must be instantiated anew.

## 1. What the dominant-candidate theorem actually provides

`EarlyC1SampleGame.accepted_coefficient_failure_bound` takes
`earlyC1 received = some p` and bounds failure of its 513-fibre mathematical
decoder to return the sixteen semantic coefficient columns of that `p`.
The same sample is used for all columns; acceptance may be an arbitrary
additional event. The theorem does not assert payment validity of `p`.

The mixed-C1 control proposed in this continuation uses a fixed received
lane equal to the indicator of a 16,535-fibre set. The zero tuple is the
dominant candidate on the complementary 245,609 fibres. A constant-one
minority tuple agrees on the 16,535-fibre set and can determine a zero
quotient reference there. This control is intended to test a wrong-dominant-
C1 claim; **the minority tuple is not asserted to be a valid payment**.
Neither a successful suffix nor failure to extract the dominant candidate
proves that no valid witness exists. The separate exact fixture and its
actual causal execution determine the eventual scope of that regression.

In particular, repeatedly applying the near unique decoder does not become
a list decoder for candidates agreeing on only about 3.6% of the domain.
`c1_gao.rs:recover_near` explicitly checks a global 16,535-bad-fibre cap and
returns one table; its fixed reproducibility coins are not claimed ideal
private randomness. The kernel-checked private-sample game is stronger
mathematics than that test's coins, but still targets one near tuple.

## 2. The candidate family and its fixing boundary

The useful replacement analysis object is an **unfiltered** finite family
of 26 original-code C1 messages, defined from the totalized fixed C1 received
word alone, with at least 38,228 common original-symbol agreements. This is
fixed before lambda and chi. A late 29-component tuple with that much own
support projects into it, without a per-column decoder-membership premise.
The parent continuation is proving this family/projection statement; this
audit does not duplicate or pre-certify that work.

The original C1 encoder's distinct-codeword overlap cap is 1,024 individual
symbols. Do not substitute the quotient/final-code cap of 255 fibres here.
Likewise, the family threshold is not an accepted-execution coverage theorem.
An arbitrary image-valid *batched* quotient still need not arise from an
original-code component tuple in this family.

The causal use of such a family is universal exclusion of applicable bad
events, not the assertion that every family member is a valid payment:

> For each member, if the actual accepted execution is correctly connected
> to that member's claims and helper/semantic plan, then outside the charged
> family collision events its selected residuals vanish.

An unrelated invalid family member need not satisfy the actual proof's
claims. Requiring every mathematical member to be valid would introduce a
different, unnecessarily strong objective.

| Fixing point | Analysis objects that can legitimately be fixed there |
|---|---|
| C1 commitment, before lambda/chi | Received C1, unfiltered C1 family, its semantic projections and tagged copy tuples; public variant/append index must also already be bound |
| After lambda/chi and the actual C2 commitment | Received helper words and any conditional full-tuple/helper family used for later semantic challenges |
| Before semantic theta/zerocheck/mu as applicable | The exact constraint/helper plan for those root bounds; the earlier C1 family alone does not fix adaptive C2 |
| After the sequential OOD answers, before gamma | Actual point claims and component OOD data, with their prior causal dependencies retained |
| Before kappa/tau, then response0/alpha0 | Ordinary/image relation inputs in their actual order; neither a post-alpha final nor its target is moved earlier |

The fresh challenge law is an ideal-experiment premise until the actual
resource-bounded transcript machine is connected. Distinct labels alone do
not supply that law.

## 3. What the existing V7 proofs really reuse

All paths in this table are under `AspisFormal/AspisFormal/Pool/`.

| Existing source/theorem | Reusable result | Limit for this continuation |
|---|---|---|
| `V7FixedWidth29TupleList.fixedC1TupleList`, `fixedC1TupleList_card_le_100`, `width29_member_projects_to_fixedC1TupleList` | A C1-only family and a genuine late-tuple-to-early-family projection | The old family filters through `decoder.initialDecode` and requires strict `38229 < agreement`; it cannot discharge the missing unfiltered coverage |
| `V7FixedC1CopyCollisionSecurity.fixedFamilyCopyCollisionProbability_le_card_mul` | Union over one fixed C1 family, with chi conditioned after lambda | Its source registry is the older 183-link registry. The old 3659-per-source/365900-family inventory is not a selected V8 budget |
| `V7FixedTupleSemanticSecurity` and `V7K15FixedFamilyCausalCover.failureEvidence_implies_fixedFamilyK15Failure` | Separates pre-lambda copy families from later full-tuple semantic families and routes actual failure branches | Requires membership/source/extraction/point-claim interfaces. The coherent-extraction constructor includes the old decoder and same-support premises; it does not cover missing arbitrary-oracle V8 branches |
| `V7RestoredSemanticWitness.accepted_restored_trace_implies_decoded_witness_valid` | Conditional deterministic composition to the older decoded spend relation | Strong source, extraction, claim, inactive and no-failure hypotheses; not the selected pair-forest validator nor unconditional verifier soundness |
| `NativePaymentCompiledCopyLogUpV1.helper_eq_nativeCopyRowRationalContribution_of_residual_zero` | Generic field identity for arbitrary two-slot weighted rows | Directly reusable algebra; all four denominators must be handled |
| `NativePaymentCompiledCopyLogUpV1.native_copy_rational_balance_zero_of_local_residuals`, `native_all_link_tuples_equal_outside_collisions` | Local residuals plus total/inactive helper boundaries yield rational balance; tagged equality isolates aliases outside named collisions | Instantiated for 78/75 unweighted native links, not the selected 136 public-weighted links |

`AlgorithmicCircleDecoderV7.ExactDecoderInstantiation` supplies
`initialDecode`, completeness, soundness, and an output-size bound as fields.
It does not itself construct an efficient list-decoding algorithm or prove
its runtime. Output cardinality at most 100 is not permission to enumerate
all field-valued coefficient tables or all per-column Cartesian products.

## 4. Exact next deterministic bridge: the selected weighted copy registry

Source anchors:

- `crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs`:
  `link_weight`, `accumulate_endpoint`, `copy_residual`, and
  `evaluate_with_selectors`.
- `pair_forest_copy_terminal_constants.rs`: 136 links, 14 tuple patterns,
  fixed producer/consumer slots and active row masks.
- `pair_forest_trace.rs:pool_v1_pair_forest_copy_rows_v1`: independent host
  registry/row construction.
- `pair_forest_constraint_residuals.rs:append_copy_residuals`: the literal
  2,176 scalar alias residuals.

Each link has public weight 0 or 1 determined by the bound variant and
append-index bit. Define its active-link subtype from that public predicate.
Only active links belong in the producer and consumer multisets. The desired
conclusion for all links is
`weight * (producer_limb - consumer_limb) = 0`, **not** unconditional tuple
equality on inactive links. This agrees with the host residual evaluator.

A focused `SelectedCopyLogUpAliases` leaf can prove the following chain for
the same arbitrary candidate table, with no honest-trace or decoder premise:

1. The literal source-shaped two-slot row and selected Boolean active mask,
   plus zero local copy residuals, imply each active helper row equals its
   weighted rational contribution, outside all relevant denominator poles.
2. The exact total-helper-zero and inactive-helper-zero boundaries imply
   zero global active-link rational balance.
3. Outside a chi collision and a lambda tagged-tuple-compression collision,
   active compressed multisets and then active tagged multisets coincide.
   The selected tags are unique, so every active tuple matches its own
   partner. Expanding its frozen pattern yields the weighted scalar aliases.
4. Specializing transfer tags `1124073483` through `1124073489` gives the
   seven aliases consumed by `SelectedAmountEndpoint`, and the same registry
   yields the occupied-note and selected path/append aliases already used in
   the other deterministic leaves.

The seven amount links are, respectively:
`44:0 -> 1008:10`, `460:0 -> 1010:10`, `508:0 -> 1012:10`,
`1008:10 -> 1014:0`, `1010:10 -> 1014:1`,
`1012:10 -> 1015:1`, `1014:2 -> 1015:0`.

Two source details must remain explicit in this port:

- The compiled evaluator accumulates a slot's compressed value even when
  that link's public weight is zero. Discarding a zero-weight link from the
  rational sum does **not** justify forgetting that factor when dividing
  the cross-multiplied local residual. Include its actual denominator pole,
  or prove a separate cancellation argument. Empty slots also require the
  chi-zero boundary. No old active-only pole inventory is imported here.
- The host row builder locates slots using zero weights; the compiled
  constants have fixed slots. Their relevant weighted rational behavior and
  residual correspondence need to be proved or compared at the precise
  chosen interface, not equated by name. Existing source identity tests and
  `SelectedSelectorExpansion` provide useful components, not a translated
  Rust loop theorem.

The required local residuals and helper boundaries are substantive explicit
prerequisites. The later probability theorem must derive them from the actual
repaired semantic/relation execution. In particular, do not restore the old
`inactiveExact` assumption as an unproved acceptance consequence. This
proposed deterministic bridge does not by itself charge lambda, chi, semantic,
or relation errors.

## 5. Payment and access work already completed, and what is not

The endpoint is not an unnamed future validator. The following existing
leaves already derive useful modeled same-table consequences from explicit
selected constraints:

| Leaves | Established deterministic endpoint |
|---|---|
| `SelectedAmountEndpoint` | Canonical decoded positive transfer amounts and exact conservation, using the opt-in positivity pack, seven copy aliases, bitness/recomposition, and six auxiliary zero equations |
| `SelectedNoteRecovery`, `SelectedMembershipDecode` | Input key/note/nullifier, canonical direction parsing, exact 20-bit index, and the same-table pair/lane/forest path to the recorded/public anchor |
| `SelectedOutputNotes`, `SelectedOutputPair` | Both decoded output openings, change occupancy/nonzero branch, and the output pair hash |
| `SelectedAppendAfterstate` | Selected append chain, frontier checks, cursor, and recorded afterstate relative to an independently supplied snapshot |

These do not yet form one universal implication from the literal compiled
residual evaluator to every branch of `recovered_witness.rs:extract_checked`.
Concrete Poseidon/field/parser/compiler refinement and independently
authenticated caller/account/settlement invariants still matter. Some hash
leaves use a maintained `gateStep` model and explicit round constants, not a
translation of the Rust round loop. The proof's public root must still be
checked against the outer caller root before any lane-root substitution.

The mask layout is also not an arbitrary predicate choice: current opt-in
positivity reserves active cell `1014:3`, leaving 3,802 mask coordinates while
preserving the old generator's draw order. Existing mask/read-invariance
proofs and source tests cover that adapter. Neither all 3,803 historical
host-padding residuals nor all honest mask cells should be required to be
zero in the selected masked predicate.

Access is beyond a hypothetical opening oracle: `query-graph-review.md`
and `raw-c1-review.md` record a byte-preserving, typed SHA-query-graph
extractor frozen at the actual C1 commitment, totalized decoding, and
same-execution checked-payment fixtures. The graph is private extractor
input, not data recoverable from a root alone. Missing/forward preimages,
collisions, fuel, replay/source mismatches and real adversary-query coupling
remain explicit. None of these fixtures implements a complete low-agreement
list decoder for the new mathematical family.

## 6. A total checked-extraction obligation

Fix one bounded extractor `E`: it obtains the permitted root-bound data,
constructs a finite executable candidate list, and tries the literal
`extract_checked` validator with independently authenticated context. Define
`X` to mean that this machine returns a validator-accepted witness within
its declared resources. Define `V` to mean that the mathematical pre-lambda
family contains at least one canonical semantic projection whose literal
validator succeeds. For actual acceptance `A`, a disjoint bookkeeping is:

| Precedence | Accepted extraction-failure class |
|---|---|
| 1 | `A AND NOT X AND NOT Access` |
| 2 | `A AND NOT X AND Access AND NOT V` |
| 3 | `A AND Access AND V AND NOT X` |

Here `Access` is success of the exact chosen access stage. Class 3 includes
failure to enumerate a valid minority candidate, parser/subfield failure,
sampler exhaustion, and resource exhaustion; a size bound on the mathematical
family alone does not remove it. It contributes zero when any candidate
actually yields a checked witness, whether dominant or minority.
Keeping `NOT X` in every row also permits an extractor to succeed through a
valid candidate outside this particular analysis family; lack of family
coverage is not, by itself, extraction failure.

Class 2 still needs a source/event decomposition: off-quotient-family finals
use only the existing theorem's applicability conditions; represented
quotients without a covered original component tuple remain visible; and
component, copy, semantic, public-binding and payment-decoding failures must
be connected without assuming their success. The near-gamma bound covers its
stated bad-binding event, not all of Class 2. The quotient outside-family
bound likewise does not charge every represented wrong-dominant-C1 proof.

For list extraction, the next executable contract is a bounded `enumerateC1`
that takes only the authenticated totalized word and public code parameters,
returns at most the proved family limit, and includes every relevant covered
candidate (or reports a separately accounted failure). A naive product of
26 component lists is not such a runtime guarantee. A checked-witness loop
over an already complete list needs at most that many validator calls; the
cost and completeness of obtaining the list are still unproved. Canonical
M31 descent must come from actual received agreement and the code, not from
assuming the recovered QM31 coefficients happen to be base-field values.

No new probability, byte, CU, privacy, or FS allowance is assigned here.
The maximum body remains 40,282 bytes. The decisive next deterministic
experiment is the selected weighted Copy LogUp bridge above; the decisive
extractor experiment is a genuine minority-valid-payment control with an
explicit bounded candidate-generation method, not another favorable suffix
or a dominant-only recovery round trip.
