# S4 head forward execution continuation

Target remains `OraclePortHeadlineFrozen2PerAttempt.final_soundness` and `AcceptedRunJoin` for `dV_frozen2`. These are focused source-model arithmetic results, not closure of S4 or of the implementation-linked headline.

Proved and committed on research:

- `17e1ac864`: actual head limb multiply/add/update forward execution, then phase-sensitive output bounds.
- `af1d4b03b`: generated eight-limb head loop forward execution via symbolic induction on remaining limbs. Canonical coefficient/scalar and incoming uniform/suffix bounds imply source loop success and the outgoing `(k+1)*cap` bound.
- `ae82b444f`: actual query-values caller success links to generated four-dots success and all four callback traces on the same mapped coefficient array and exact 608-byte query prefix.
- `c55b7c52c`: actual checked offsets, slice, four-byte array conversion, and coefficient read from slot<4 and term<26; full per-term assembly derives inner-loop success from bounds.
- `5e1203117`: carry each callback's existing exact source-field functional result through the caller join without dependent elimination of its large payload.
- `7e3e8e6cb`: install the retained strict M31 parser, exact wide-to-limbs operation and eight-limb constant into the actual per-term body. Derive scalar and coefficient bounds and conversion/inner-loop success. Remaining inputs: exact parser acceptance, canonical selected Wide coefficient, and incoming k-cap bound.

Each root packet records compiler/source/object hashes, launch revision, command, focused exit status, wall time, peak RSS, swap and standard-axiom reports. No production Rust source changed. No full manifest replay or CU gate was repeated.

## Further proved execution composition

- `7d8eda38f`: full bounded per-batch term loop, deriving each selected coefficient's canonicality from the original array.
- `9d474e32c`: actual partial-fold limb body and complete eight-limb loop. This uses a deliberately coarse execution envelope to construct every checked call; tighter retained per-coordinate semantic bounds remain separate.
- `e746e660e`: complete actual outer batch body, including checked range selection and both inner loops.
- `0e3508549`: full actual outer head loop, deriving the StepBy calls and using induction on the remaining batch count.
- `822586212`: initialized seven batches from the actual zero limb array and source iterator initialization. Exact strict parser acceptances for 26 head records and canonicality of the 29 coefficient inputs remain premises. Every head arithmetic and loop success is derived. The coarse final bound is `56 * (2^34 - 1)`, safely within U64.

Adjacent integration: `88ecb5afb` adds concrete EbyK new/first-push/finish product semantics; `766e0ffec` installs the genuinely extracted current wide-QM multiplication into scalar-factor operations; `02af43782` adds ClaimPowers carrier transport and a typed tx2 powers-to-query-loop same-array cut. These do not close their explicit source/Std/caller boundaries.

## Complete current-model execution now constructed

- `0636a676f`: generic bounded callback forward execution for the retained stateful P6 array model, including length and value predicates.
- `5049c48e3`: actual generated N8 reducer callbacks succeed for arbitrary typed head limbs and produce canonical words.
- `0203329cc`: every canonical eight-word array is accepted by the retained current from-limbs operation; full `HeadCore` initialization/loop/array/packing chain is constructed for one operations record.
- `542fe958f`: the actual generated single dot callback executes head, three concrete tail pushes, finish and current wide addition, returning a canonical value. No child-call success is a premise.
- `2db33fa95`: all four actual callbacks construct the N4 array with canonical outputs.
- `b5390af4a`: complete generated `four_dots` executes through its actual608-byte slice/shared-array conversion and N4 callback array.

The last theorem is `AspisR1FastDotsFunctionForwardRootV1.four_dots_forward`. Its remaining inputs are query length≥608, exact608-byte prefix array identity, canonical29-entry coefficients and `SlotInput` for each of four slots. `SlotInput` contains strict parser acceptances on the exact source-read bytes. It assumes no callback, loop, push, finish, array or addition success. Array construction is explicitly the retained P6 model, so this is **not** final Rust/frozen-source refinement or closure of S4.

## Next source/semantic joins and principal extraction blocker

1. Bind the exact prefix/SlotInput and coefficient premises to the frozen caller's source operations and admissible proof bytes. Reuse ClaimPowers coordinate transport and same-array tx2 cuts, without treating a typed cut as full current tx2 refinement.
2. **Current-model execution/field join proved.** `S4ForwardFieldOpsRootV1.forward_field_ops_same` proves the installed records equal when the old adapter selects P6 for all fallback array lengths. `S4ForwardFieldMeaningRootV1.four_dots_forward_field_meaning` constructs the complete function result, canonical outputs and four `CallbackFieldResult` facts for those same outputs and exact prefix/coefficient inputs. No parent or child success premise, independent existential matching, or Ops equality premise is used. The final accepted-run/source endpoint is still open.
3. **Shared P6/Std source correspondence remains real.** Actual Rust `array::from_fn` goes through `try_from_fn` / `try_from_fn_erased` and a mutable MaybeUninit buffer. Retained attempts leave the child external or fail at `push_unchecked`; callback scheduling proofs do not prove that buffer implementation.
4. Candidate-only extraction has found alternatives. The retained exact initialized-loop powers candidate already has an all-N recurrence proof; fresh N29 extraction confirms feasibility (`db1632d37` packet). S4 candidate v8 successfully emits a nonempty full function after replacing from_fn with initialized arrays, a bounded outer loop/by-value Copy helper and explicit fixed-size inner operations. Its change list is larger than a two-call substitution. V9's dynamic final N8 array write still fails Aeneas borrow replay. NUC optimized candidate measurements are now retained: v8 maximum 1,212,876 CU; smaller fixed-call v10 maximum 1,212,366 CU against a 1.4M budget. All six finite fixture output hashes match their baseline and strict stack checks pass. Both regress relative to baseline (v10 roughly +13.1k stage1/+15.7k settlement). The baseline has an explicit 58-path source/features coverage caveat; these are measurements, not analytical worst-case bounds. **No candidate adopted, frozen source changed, or frozen-source equivalence proved.**
5. Full accepted-run/source/runtime and final artifact joins remain required. Keep the global100-bit objective active.

## Cache and focused runner locations

Root sources/objects and exact evidence are under `/tmp/root-s4-head-limb-forward-v3-20261021`, `/tmp/root-s4-head-loop-forward-v3-20261021`, `/tmp/root-s4-head-read-forward-v2-20261021`, `/tmp/root-s4-head-term-forward-v1-20261021`, and `/tmp/root-s4-current-head-term-forward-v1-20261021`. Packet sources/receipts are committed under `evidence/s4-*-forward-root-v1-20261021/`.

Prepend the retained Formatter repair closure before other Aeneas cache owners; reject any audit containing `core.fmt.Formatter`. This repair is a retained P6 model, not a proof of Rust Std correspondence. Use exact Lean 4.32, `-j1 -M4400`, owned mkdir lock and a live-process admission check; preserve unrelated live worktree edits.

Latest root warm objects: `/tmp/root-s4-head-batch-terms-forward-v2-20261021`, `/tmp/root-s4-limb-fold-forward-v5-20261021`, `/tmp/root-s4-limb-loop-forward-v2-20261021`, `/tmp/root-s4-head-batch-body-forward-v3-20261021`, `/tmp/root-s4-head-outer-forward-v3-20261021`, `/tmp/root-s4-seven-batches-forward-v1-20261021`, each under `objects/` with matching `sources/` and `evidence/`. No binary is committed.

Latest root complete-execution sources/objects/evidence: `/tmp/root-s4-p6-array-forward-v3-20261021`, `/tmp/root-s4-n8-output-forward-v1-20261021`, `/tmp/root-s4-n8-pack-forward-v2-20261021`, `/tmp/root-s4-head-core-forward-v1-20261021`, `/tmp/root-s4-full-callback-forward-v3-20261021`, `/tmp/root-s4-four-callbacks-forward-v1-20261021`, `/tmp/root-s4-function-forward-v1-20261021`. All green targets audited to standard axioms, with no production mutation or manifest-wide replay.

## Latest focused joins

Packets `evidence/s4-forward-field-ops-root-v1-20261021/` and `evidence/s4-forward-field-meaning-root-v1-20261021/` contain exact sources, direct-import pins and focused receipts. Operation equality: 47.714 seconds / 2,701,541,376 bytes peak process RSS. Complete execution/field join: 12.640 seconds / 3,635,544,064 bytes. Both exit0, zero swaps, standard axioms only. Failed local operation-equality tactic attempts are retained as diagnostics, not accepted proofs. No full manifest or unrelated runtime suite ran.

Adjacent S5: `evidence/s5-paircut-range-loop-trace-v1-20261021/` proves successful actual range-loop execution yields an ordered callback trace. `evidence/s5-paircut-range-decoded-product-v2-20261021/` retains that same trace, the accepted push list, and a `List.Forall₂` mapping of each index to the exact successful reader/scratch pair. Its decoded finish equation uses that same product list. The checked-field specialization derives successful-read canonicality; the external generated reader binding remains open. The earlier v1 product packet omits the exported list/read correspondence and is superseded for this purpose.

Next: concrete caller input provenance and the Rust Std/from_fn boundary. The latter is not closed by any P6 scheduling theorem or by candidate fixture agreement.

## Literal value equations

`S4LiteralHeadSumRootV1.source_head_sum_literal` removes execution-selected head lists from the value expression: exact ordered source coverage and source meanings imply the fixed 26-term sum of coefficient reads times the raw little-endian source words at their exact slot/term byte offsets. The invalid-shape default in the total value function is excluded by each source meaning.

`S4LiteralCallbackValueRootV1.callback_field_result_literal` composes that identity with the same callback field result, retaining the actual first tail input, g[28] read, two-term tail run and accepted three-push trace. `S4ForwardLiteralValueRootV1.four_dots_forward_literal_value` constructs the entire function result and supplies these literal value equations for its same four canonical outputs. No child-call, array-call or parent execution success premise is introduced. The remaining parser/canonicality, P6/Std and actual caller/source/runtime boundaries are unchanged.

Focused targets: literal head sum 17.356s / 3,681,206,272B RSS; literal callback 20.107s / 3,668,688,896B; complete forward literal values 17.329s / 3,641,311,232B. All exit0, zero swaps and standard axioms. The source-only focused packets retain direct dependency sources and exact receipts; no full manifest or unchanged CU run was started.

## Canonical scanner to actual head parser

The lead's newly landed `MultiproofConeStrictScan.scan_total` proves the strict scanner matches the frozen compact canonical-byte model. Reusing its canonical/endian owner, `S4CanonicalHeadWordRootV1.current_m31_parser_forward` now proves actual current M31 acceptance from the same four bytes' literal little-endian bound. The array-byte carrier equality is proved explicitly.

`S4CanonicalHeadInputsRootV1.canonical_all_head_parsed_at` constructs the checked source read for every slot<4 and head term<26, identifies it with canonical word index `slot*30+term`, and derives strict parser acceptance. This removes all 104 independently supplied head parser successes when consuming a canonical608-byte payload. No coefficient canonicality is needed just to construct these byte reads. Actual opening/prefix/stored-proof identity, twelve QM tail acceptances, coefficient provenance and P6/Std remain open; the full `SlotInput` premise has not yet been discharged.

Focused canonical-word target: 13.473s / 3,963,617,280B peak RSS; complete head input binding: 19.598s / 3,811,246,080B. Both exit0, zero swaps, standard axioms. Reused lead source matches its exact producing source SHA. Failed environment/tactic attempts and the selected lead cache provenance are retained. Next: derive the QM tail parser facts from the same canonical payload, then bind the complete SlotInput to the strict scanner and actual opening reader.

## All strict decoder premises discharged for canonical openings

`S4CanonicalQmWordRootV1` reuses the merged canonical take/drop theorem and retained strict QM parser refinement to prove each sixteen-byte source slice is accepted. `S4CanonicalSlotInputsRootV1.canonical_slot_input` constructs the actual first-tail/two-loop read witnesses and supplies every SlotInput from the one canonical608-byte payload predicate. Thus all116 decoder successes are derived, including all12 QM tail values; none remains a separately supplied premise at this layer.

`S4CanonicalOpeningForwardRootV1.four_dots_forward_of_canonical_opening` now constructs the complete four-dot result, canonicality and literal source equations from openingCanonical, exact typed prefix identity and29 coefficient bounds. It also derives query length≥608 from the typed prefix identity. Remaining: connect the actual stored proof / opening reader to this canonical opening predicate; connect the29 coefficients to the same successful powers; replace/justify P6 array construction and install actual caller/source/runtime/artifact bindings. This is not closure of S4.

Focused receipts: QM byte/codec 56.842s / 2,894,544,896B RSS; complete SlotInput34.848s / 3,803,791,360B; complete canonical-opening consumer28.127s / 3,879,043,072B. All exit0, zero swaps and standard axioms; no full manifest replay or unrelated CU gate. Exact lead canonical append source matches its producing source hash.

## Scanner-bound complete four-dot result

`S4ScannedOpeningForwardRootV1.strict_scan_accepted_opening` reuses the merged strict scanner theorem to derive canonicality of the exact indexed832-byte opening from owned scanner acceptance, the57607-byte proof length, j<22 and the same source slice identity. `four_dots_forward_of_scanned_opening` consumes that derived fact and constructs the complete P6 four-dot output, canonical outputs and literal field equations. No opening canonicality, decoder success or child execution success is supplied independently.

The source-only packet is `evidence/s4-scanned-opening-forward-root-v1-20261021/`. Focused Lean4.32 check: exit0,20.455s,3,881,418,752B peak process RSS,zero swaps, standard axioms only. The direct scanner source matches its producing receipt; the first failed local decidability tactic attempt is retained. This is an owned-reference/P6 result: actual production scanner correspondence, stored-proof/opening/prefix identity, coefficient provenance, Std/runtime/caller/artifact joins remain open. No full manifest or CU rerun.

## Same-input ClaimPowers composition

`S4ScannedClaimPowersForwardRootV1.four_dots_forward_of_scanner_and_claim_powers` reuses the existing Claim-to-FastDots fieldwise carrier proof. It replaces29 independent coordinate-bound inputs with canonical gamma, successful ClaimPowers and the explicit identity of the coefficient array with that same mapped output. The scanner, prefix, complete execution and literal results use the same proof/opening/coefficient witnesses. This is a composition with different, concrete provenance premises, not a claim that the caller identity has been proved.

Source-only packet `evidence/s4-scanned-claim-powers-forward-root-v1-20261021/`: focused exit0,34.600s,3,772,235,776B peak process RSS,zero swaps,standard axioms. Exact imported coordinate source/object match its existing producer manifest. One missing-object cache-order failure is retained; the corrected run selects the existing complete namespace closure, with no dependency rebuild. Actual frozen powers/source/caller, stored-proof/scanner and P6/Std/runtime/artifact joins remain open.

## Accepted-run prefix and same-output field meaning

`S4ScannedAcceptedRunRootV1.four_dots_success_exact_prefix` reuses the generated function's first three bind inversions and exact slice/try-from/unwrap operations to derive the typed608-byte prefix from any successful generated four-dot call, for arbitrary Ops and without coefficient hypotheses. `scanned_accepted_run_literal_values` applies this to the installed P6 call, reuses the scanner/ClaimPowers construction and identifies its output with the accepted output by Result.ok injectivity. Every literal field result and canonicality fact describes those same accepted values.

The accepted-run theorem replaces the independently supplied prefix identity with successful selected execution. This is a different accepted-run statement, not a claim of stronger unconditional totality or proof of the caller. Source-only packet `evidence/s4-scanned-accepted-run-root-v1-20261021/`: exit0,20.202s,3,920,904,192B peak process RSS,zero swaps,standard axioms. Actual opening/scanner/powers/caller bindings, P6/Std and runtime/artifact joins remain open.

## Query-prefix caller composition

`S4ScannedQueryPrefixRootV1.scanned_query_prefix_success_literal_values` composes the retained typed query-prefix adapter with the scanner-bound accepted-run theorem. It derives the query-index read, cast, opening call, same coefficient forwarding and exact returned tuple; the same accepted dot array supplies canonicality and all four literal field results. It does not introduce independent callback or arithmetic success witnesses.

The opening operation still has an explicit successful-read byte-offset contract on the same proof and `next`; `next<22`, canonical gamma, successful ClaimPowers and its same-array carrier identity remain inputs. `query_values_forward_prefix_ops` is a selected prefix model, so this composition is not full frozen query_values/tx2 source refinement. Production scanner/opening, powers/caller, P6/Std and runtime/artifact joins remain open.

Packet `evidence/s4-scanned-query-prefix-root-v1-20261021/`: focused exit0,47.985s,3,261,661,184B peak process RSS,zero swaps,standard axioms. Exact prefix-adapter source/object pair matches its existing producer manifest; unchanged dependencies were reused.

## All-outcome tail equivalence

`S4TailLiteralEqualityRootV1.actual_tail_eq_literal_two_pushes` proves exact Result equality between the original generated tail loop over0..2 and the candidate literal two-push model, for arbitrary typed inputs and operation records. The proof reuses the exact literal operation sequence and next/body equality, then unfolds only the two range steps and terminal state. It covers success, failure and divergence without parser, coordinate, accumulator invariant or execution-success premises. `literal_two_pushes_success_actual_tail` supplies the previously missing reverse success direction.

This closes the one-way tail-model comparison, not raw candidate type/operation correspondence or full frozen helper equivalence/adoption. Packet `evidence/s4-tail-literal-equality-root-v1-20261021/`: focused exit0,10.370s,3,683,172,352B peak process RSS,zero swaps,standard axioms. Two failed local match/let presentation attempts are retained; no source/toolchain or cap change, no full replay or CU rerun. The copied literal definitions/body helper match the prior retained source exactly up to enclosing namespace.

## Complete fixed-call head-loop transfer

`S4FixedHeadLoopTransferRootV1.fixed_head_loop_success_old_head_loop` transfers every successful complete fixed-call head loop to the original generated head loop with the same inputs, iterators and returned limb array. It reuses `fixed_batch_body_success_old_body` for continuations and the exact terminal branch; induction follows the retained StepBy cursor progress. Its only operation/iterator premises are wideLimbCount=ok8 and step_by=4. No canonicality, parser or independent original-loop success is supplied.

This extends the per-batch bridge to the whole head loop. Eight-value output packing, the complete helper/outer function and raw V10/source type/operation binding still need composition; the all-outcome tail equality is already proved separately. Packet `evidence/s4-fixed-head-loop-transfer-root-v1-20261021/`: focused exit0,3.102s,2,273,394,688B peak process RSS,zero swaps,standard axioms. First local pair-let/syntax presentation failure retained. The selected progress import is cache/preflight-pinned while its old source producer lists a different object hash; final coherent source/object replay is still required and no release source re-pin is claimed.

## Literal N8 read/reduce packing

`S4LiteralN8PackingRootV1.literal_eight_success_p6_same_output` constructs the original P6 N8 array success from the eight literal read/reduce operations' success, preserving their exact returned values. It derives bounded callback totality, reuses generic P6 forward execution, then uses the retained indexed N8 output theorem and deterministic reads/reductions to identify the constructed array. No canonicality or independent array success is assumed.

This closes the local literal-N8-to-P6 output gap needed by the complete fixed-call helper comparison. Extracting that grouped literalEight segment from the complete candidate helper and composing head/tail remain next. Packet `evidence/s4-literal-n8-packing-root-v1-20261021/`: focused exit0,12.451s,3,745,873,920B peak process RSS,zero swaps,standard axioms. The older source replay and selected warm object are separately pinned with differing historical object hashes; final coherent release replay is still required. No production/CU change or whole-helper/source adoption claimed.

## Concentrated closure: complete helper and four-output composition

All four workers were redirected to S4 on 21 October; the focused checkpoint
clock was recorded at 16:48 UTC (review by 18:48 UTC). This changes allocation,
not the security target or the meaning of cone closure.

`S4FixedTailProgramEqualityRootV1.fixed_tail_eq_old_tail` proves all-Result
equality of the complete fixed-helper and original scalar tail programs.
Source-cut checks compare both exact generated bodies, modulo argument names
and projection of the old captured-array tuple. Focused exit0,16.329s,
3,288,072,192B peak RSS,zero swap,standard axioms.

`S4WholeHelperTransferRootV1.installed_fixed_helper_success_old_callback`
composes the complete head transfer, literal N8 packing and full tail equality.
Its only execution premise is successful fixed-v6 helper execution under the
retained concrete installation. It returns the identical scalar and unchanged
captured arrays from the original callback. The installation discharges the
generic limb-count and P6 N8 operation equalities. Focused exit0,25.412s,
3,586,605,056B peak RSS,zero swap,standard axioms.

`S4WholeOuterTransferRootV1.installed_fixed_four_success_old_four` then builds
the exact ordered four-callback P6 trace and original array from the complete
fixed-call function's accepted execution. No independent old callback,
constructor or parent success is assumed. Focused exit0,20.501s,
3,645,177,856B peak RSS,zero swap,standard axioms.

`S4FixedFourScannedMeaningRootV1.fixed_four_scanned_literal_values` feeds that
same complete output into the retained scanner-bound arithmetic theorem.
All four returned values have the literal source field equations and are
canonical. Focused exit0,26.672s,3,861,217,280B peak RSS,zero swap,standard axioms.

The packets are respectively `s4-fixed-tail-program-equality-root-v1-20261021`,
`s4-whole-helper-transfer-root-v1-20261021`,
`s4-whole-outer-transfer-root-v1-20261021`, and
`s4-fixed-four-scanned-meaning-root-v1-20261021` under `evidence/`.

**S4 remains open.** These are selected-model accepted-run results. Required
source work is the complete typed V10 helper/outer transport, concrete emitted
operation/type bindings, actual opening/caller and coefficient provenance,
and a concrete frozen component/driver connection. The existing shared S10
model inventory still has a placeholder S4 carrier/implementation; its generic
ConeJoin cannot be instantiated merely by renaming these local results.
The frozen Rust still uses `array::from_fn`; P6 is an intermediate model,
not a completed Rust Std proof. Candidate adoption or that source boundary
must be resolved before a frozen-implementation closure claim. No production
code, wire format or runtime artifact changed in these commits.


## 18:07 UTC — complete typed helper, outer call and query consumer

The previous paragraph's typed helper/outer and actual opening/caller items
have materially advanced, without changing the remaining release boundary.

- `S4V10LiteralHelperSourceCutV1.literal_helper_eq_fixed` identifies the entire
  emitted V10 helper, through named typed operation substitutions, with the
  current fixed-v6 helper for **all Result outcomes**. Its checker compares
  the complete emitted token stream. Focused exit 0, 8.74s, 3,756,589,056B RSS,
  zero swap, standard axioms.
- `S4V10LiteralOuterTransferRootV1.literal_outer_to_current` discharges the
  complete helper relation in the exact emitted outer four-call body; no
  independent child equality/success premise remains. It preserves failure,
  divergence and the exact mapped four-element output. Focused exit 0,
  7.818s, 3,705,798,656B RSS, zero swap, standard axioms.
- `S4V10LiteralScannedMeaningRootV1.literal_four_scanned_literal_values`
  transfers that same output to all four literal field equations and
  canonicality. Retained premises are gamma canonicality, the ClaimPowers
  output/caller identity, scanner success and the opening/length/index facts.
  Focused exit 0, 12.773s, 3,992,518,656B RSS, zero swap, standard axioms.
- `S4FullQueryValuesPrefixV1.full_query_values_success_scanned_field_results`
  consumes success of the **complete** retained `queryWithOps` source cut,
  with installed S4 and actual R22 opening. It derives the opening, index
  bound, exact 608-byte prefix and same four returned field-result witnesses.
  Thus the length/index/opening and separate dot-success assumptions are not
  independent caller premises. Gamma, ClaimPowers output and coefficient
  identity remain explicit. Focused exit 0, 18.61s, 4,006,363,136B RSS, zero
  swap, standard axioms. The non-S4 query operations remain parameterized;
  this is not yet the complete frozen caller refinement.
- `S4InstalledOpsIndependentRootV1.installed_ops_independent` proves the
  **entire eleven-field installed record** is independent of its apparent
  base argument. The selected model has no arbitrary backend left through
  that base. This does not identify those fixed methods with Rust execution.
- `S4DotPushCallEqualityV1.dot_via_raw_eq_generated_push_raw` identifies the
  installed dot backend with the retained generated dot-loop adapter for
  every Result outcome. It retains the raw-function and Rust Std lineage
  boundaries; it is stronger than the earlier push-count result.

These packets are committed through `38fd90a6c` on research. No production
source, protocol parameter or release artifact changed.

The decisive remaining S4 boundaries are concrete, not more head arithmetic:

1. **Frozen source/Std:** original `from_fn` has no accepted extracted parent
   owner. The transparent LLBC attempt fails at the mutable limb loop before
   Aeneas emits it; the P6 trace theorem is about the model. V10 avoids this
   source construct but is still a candidate requiring adoption and gates.
2. **Accumulator child:** Rust `Iterator::all` has no retained Aeneas method
   owner. A minimal candidate replaces only Q::from_limbs with four ordered
   comparisons; native differential partitions/boundaries/random arrays pass,
   while its generated-source/Lean proof is in flight. No adoption is claimed.
3. **Coefficient provenance:** retained tx2 source proves the same g is
   passed from powers29 into the query loop. Current powers29's Std/borrowed
   callback parent has no accepted whole-array source owner equating that
   output with ClaimPowers. Per-step arithmetic alone does not discharge it.
4. **Final composition:** instantiate the complete concrete component and
   actual driver interfaces at an adopted source/artifact pin, then perform
   the coherent closure replay. The S10 placeholder does not establish this.

**S4 is not closed; the 100-bit implementation-linked target is not yet
established.** All four workers remain allocated to the above source and
composition boundaries, rather than restarting S3/S5 arithmetic inventories.

## Two-hour checkpoint — 18:49 UTC

**S4 remains open.** Concentrating the four workers has produced checked
compositions covering all ten stage-1 queries and all twelve stage-2 queries,
not just isolated dot-product examples. These are candidate/model source-cut
results, not closure of the frozen Rust component or the global driver.

The twelve-query result now derives the coefficient array from the same
successful tx2 prefix. Its early-indexed-powers variant invokes the retained
transparent extracted candidate directly; it does not assume Rust
`array::from_fn` correspondence. Likewise, the first-ten-query result derives
canonical gamma and the coefficient array from one successful candidate-backed
preparation and uses that same returned scratch array. The actual tx1 parent
link remains separate. These results are in the early-powers prefix and
prepared-scratch early-indexed-powers packets under `evidence/`.

Concrete typed source bindings now cover the installed QM31 parser,
WideExact to/from-limbs and addition, and the checked-Q/dot-push child. The
four-comparison Q candidate has a generated-body equivalence theorem and
optimized native differential tests. Its proof does not require an arbitrary
iterator predicate or arbitrary dot backend. Rust Std/runtime boundaries
listed in the packets are not thereby proved.

An important scope correction: the fixed-tail/original-tail equality preserves
all Result outcomes. The existing complete fixed-head/original-head bridge is
only **successful fixed execution implies matching original execution**.
The reverse success direction and totality are not consequences of that
theorem. The reverse-loop worker has now proved that a successful original
limb loop yields an ordered symbolic trace of exactly `end - start` steps;
identifying its eight-step specialization with the fixed emitted sequence is
in progress. Literal eight-element packing itself has a checked totality
lemma.

The proof-friendly combined source candidate changes only `fast_dots.rs`,
`fast_pairing.rs` and `weights.rs` in an isolated worktree; research production
source is unchanged. Six fixtures and the strict stack gate pass functional
checks, with maximum measured stage-1 CU **1,210,100** and settlement CU
**1,189,265**. These are fixture measurements, not all-input bounds. The
candidate fails the existing preregistered B1 CU criterion on all six fixtures;
no budget relaxation or adoption is claimed. A single additional inline
variant was more expensive and has been stopped. The cheaper candidate's
remaining standing gates are running sequentially on the capped NUC.

Remaining closure work is: reverse-loop/totality composition; actual parent
caller and source-operation bindings; an explicit decision on candidate
adoption versus frozen-source correspondence; then the concrete component and
driver interfaces with the appropriate source/artifact pins and one coherent
closure replay. The S10 model placeholder remains a placeholder. The two-hour
checkpoint did not meet full S4 closure, and no new closure ETA is asserted.

## 19:48 UTC — complete selected arithmetic, caller dataflow and library evidence

The reverse execution gap is now discharged for the selected operation chain.
The original eight-coordinate accumulation loop and the eight-coordinate limb
fold each supply ordered successful segment traces. Their concrete reverse
bridges feed the term loop, complete batch body, StepBy head loop, complete
helper and all four outer calls. `S4ConcreteReverseClosureRootV1` therefore
proves `installed_reverse_head` and `fixed_four_total_on_slots` without the
former reverse-loop or independent successful-helper premises. Its checked
composition exited 0 in 23.846s, peak process RSS 3,602,808,832B, zero swaps;
all five printed declarations report standard axioms. This is committed at
`68580ee4f`; the supporting trace packets are retained at `fd299254f`.

`S4TotalScannedFieldResultsRootV1.fixed_four_total_and_field_results_from_scan`
now derives **both execution and all four exact field-result witnesses** from
the strict scan, a canonical gamma, its successful ClaimPowers result and the
same caller coefficient array. It constructs the exact 608-byte prefix and
derives all coordinate/read/parser witnesses internally. No successful dot
call, reverse-loop law, independent prefix or per-slot acceptance premise is
assumed. Focused exit 0, 18.682s, peak process RSS 3,856,334,848B, zero swaps,
standard axioms. The packet and the literal-V10 totality consumer are committed
at `1ce5cc09b`. The literal consumer preserves the mapped four-element output;
its own unmeasured swap is explicitly recorded UNKNOWN.

The current frozen tx1 parent extraction already existed and has been reused:
caller-v4 has transparent `tx1` and `prepare`, with `has_errors=false`, against
the frozen `candidate.rs` SHA-256
`5164975df10f79e9810f9321b8130a9865eb9bb9b6b9de7011f4359ece98c794`.
The complete-body Ops cut retains all branches and Std Try/residual handling;
its checker expands the factored suffix and verifies all tokens after 15
explicit child/constant substitutions. The theorem
`tx1_success_same_prepare_and_query` derives a successful query-loop call with
the **same prepared value and scratch array** returned by that run's prepare.
It does not assume the query call succeeds independently. Its exact operation
bindings remain open. Packet `s4-current-tx1-same-prepare-query-v1-20261021`,
commit `da9c08428`, records standard axioms, child time 15.56s, runner elapsed
15.829s, peak RSS 2,222,800,896B and zero swaps. The receipt documents its argv
metadata recovery; no unchanged proof was rerun to recover those fields.

The NUC Kani checks cover actual Std array-constructor call order/output/state
threading at sizes 4, 8 and 29, and the original four-limb Q predicate versus
the explicit four comparisons. These are bounded Rust operational results,
not Lean source-join inhabitants. Seven relevant upstream Std bodies match
between the pinned upstream 1.89 and Kani 1.93 source versions; identity with
the Solana SBF fork and the Aeneas external declaration is still unproved.
The evidence-only packet was integrated at `484174233`, preserving that
limitation rather than adopting the three-file source candidate.

The isolated candidate has now passed all 30 standing commands and its
default/devnet-ID builds have identical `.text`; only the two ID data slots
change. It still fails the existing B1 fixture CU criterion. No adoption,
budget relaxation, deployment or all-input CU claim is made. A retained
57,607-byte full-mask OS-random corpus proof has been identified for a
same-proof frozen/candidate cost control; that control is not yet accepted.

**S4 remains open at the source and caller boundary.** The next composition
maps all actual caller Prepared/scratch/accumulator/pending fields into the
retained query-loop carriers, installs that actual child slot, and connects
the resulting same-call loop witness to the existing ten-query field theorem.
The independent primitive/library, upstream preparation and final driver
bindings must still be installed at the frozen source/artifact pin. None of
the above replaces the S10 placeholder or constructs the complete
`OraclePortFrozen2Join.AcceptedRunJoin`; the deployed 100-bit target remains
unestablished. Production source and wire format remain unchanged.

## Concrete kernel and original/P6 endpoint integrated

The original/P6 scanner endpoint is committed at `a76beb8e9`: scanner and
same canonical ClaimPowers inputs imply successful original generated
`four_dots` execution and all four field-result witnesses. Its source-library
P6 correspondence remains explicit. Focused compile: exit 0, 24.210s,
3,985,752,064B peak RSS, zero swaps, standard axioms.

`S4ConcreteKernelOpsRootV1.original_four_total_and_field_results` now removes
the arbitrary Ops parameter entirely. The complete eleven-field record is
written explicitly, and both installed records equal it. The proof reuses
the scanner-total theorem and the original/fixed transfer. Focused compile:
exit 0, 12.344s, 3,966,222,336B peak process RSS, zero swaps; all three
printed declarations use standard axioms. The failed first compile was an
installer-alias rewrite mismatch; its source and logs are retained as rejected
diagnostics. No dependency replay or source migration was performed.

This completes the selected arithmetic model's operation specification, not
the frozen Rust-to-model correspondence. Actual Std/from_fn, preparation,
caller operation slots and final S4/S10 driver bindings remain open. The
100-bit implementation target is not yet established.

## Full-mask retained-proof control

The same current-format 57,607-byte OS-random/full-mask proof and public
input were accepted by both pinned frozen and isolated candidate artifacts.
Source-only evidence is integrated in
`evidence/s4-full-osmask-current-cu-control-v1-20261021/`, preserving the
original corpus provenance and exact input/artifact hashes.

Measured stage-1 transaction CU: frozen 1,196,068; candidate 1,206,885
(delta 10,817). Measured settlement transaction CU: frozen 1,139,924;
candidate 1,150,423 (delta 10,499). The nested verifier CPI is included in
the settlement total, not an additional transaction. Both runs exited 0
under capped zero-swap scopes. This answers the requested single full-mask
control, but proves neither cost independence from masks nor a worst-case
bound. The candidate remains unadopted and still fails its existing B1
fixture criterion. No production source or release budget changed.

## Caller query state, split guard and exact library source

At `d773d87db`, the checked caller/Stage2 carrier packet maps all actual
Prepared, scratch, accumulator, geometry and pending-weight fields and
derives the same successful Stage2 query-loop call from successful current
tx1 control flow. The source-installed constructor variant derives its
initial next=0 from that same execution without an independent constructor
result or equality premise. Binding the actual generated constructor slot
to that transparent source body remains open: its current emitted owner
marks Accumulator::new opaque. A focused constructor-root extraction is
being attempted instead of accepting that source-slot equality as assumed.

The split-guard theorem independently derives k=ops.split directly from the
first rejecting guard in the complete retained tx1 source cut. Instantiating
only the frozen compact.rs literal split value derives k=10. Focused compile
exit 0, 2.167s, peak process RSS 2,246,852,608B, zero swaps; both printed
declarations have standard axioms. The new ten-query composition therefore
need not assume either the starting cursor or the admitted split. Its first
combined imports exposed a real generated global-discriminant instance name
collision; a namespace-only source adapter and focused dependent rebuild
are in flight. No combined theorem is claimed green yet.

At `1c541c92c`, exact SBF std source provenance supersedes the earlier
source-unavailable limitation. Installed core/array/mod.rs and try_trait.rs
match Anza commit 790f1537507dbdb0da320fbb3b1c1eca3b33c474, as pinned by
platform-tools v1.52 version.md. Seven relevant bodies match the prior
Kani/upstream comparison. This is source identity, not formal refinement;
the compiler binary itself still reports an unknown commit.

The isolated Std extraction now exposes an Aeneas associated-type
normalization error at Try::Output, independently of S4 arithmetic. The
original failure and supported-mode probes are retained, and a type-safe
normalization repair is under investigation. No weakened equality check,
custom axiom, source migration or original-Std correspondence claim is
accepted. S4 and the full implementation-linked 100-bit theorem remain open.

## Focused S4 caller composition and candidate refinement

At `2498c28cc`, `source_tx1_success_ten_field_results` composes one
source-installed caller success with all ten ordered query executions and
their four field-result witnesses. The preparation and strict-scanner
contracts remain explicit and are applied to results from that same caller.
The arithmetic record is concrete. Its constructor predecessor is still the
source-installed constant model; this does not close the frozen caller slot.
The focused compile passed in 29.32 seconds, peak process RSS
3,894,444,032 bytes, zero swaps, standard axioms. Keeping already proved
query functions locally irreducible avoided pathological definitional
reduction; no resource-option override was introduced.

The concrete V10 endpoint and the full-query accepted-result refinement
are checked. A further concrete QueryOps builder fixes the dots callback
to the literal V10 outer body, and generic ten/twelve-query loop transport
preserves the identical final output. Their source-only packets are
`s4-v10-concrete-queryops-builder-v1-20261021` and
`s4-stage2-querycall-refinement-v1-20261021`. These are model/refinement
results, not candidate adoption or frozen Rust execution equivalence.

The isolated current constructor extraction succeeded using an added
wrapper in a private source copy; the frozen constructor body is unchanged.
`s4-accumulator-new-current-extraction-v1-20261021` retains the generated
body and a Result-valued source cut, including failure/divergence and error
conversion. Success of that installed cut gives next=0 in the same caller
witness. Its child implementations remain parameterized. The extraction
launch Git revision was not captured; exact source hashes are retained and
this is explicitly not a final formal release receipt.

Further unsafe Std implementation lowering is not the active route. A
conservative associated-type repair passed the earlier Try-output failure
but exposed unsupported mutable-borrow copying inside Std Guard. The
already tested V10 candidate avoids this custom from_fn-model gap; it is
still unadopted and fails the historical B1 CU criterion. All four active
slots are concentrating on S4 composition and its remaining source boundary.
S4 against the frozen implementation and the full 100-bit goal remain open.

## Concrete constructor arithmetic and caller upgrade

`evidence/s4-accumulator-concrete-children-v1-20261021` supplies the
source-owned final_len and ZERO/ONE leaves through explicit carrier maps;
only filled remains universal. The current source-installed caller proof
now uses this emitted Result-valued constructor body rather than the
earlier pure-constant predecessor. The prepared-loop producer is retained
in `evidence/s4-concrete-prepared-loop-v4-20261021`.

`S4Tx1TenFieldResultsConcreteV4.source_tx1_success_ten_field_results`
(namespace `AspisR1S4Tx1ConcreteTenFieldResultsRootV4`) composes that producer
with all ten ordered model query results. It removes the previously supplied
finalLen, zeroQ, zeroWide and oneQ constructor arguments. Scanner and
same-result preparation/ClaimPowers contracts remain explicit, as do the
non-S4 operation slots. Focused compile: exit0,23.460s,peak process RSS
3,870,687,232 bytes,zero swaps,standard axioms. Its source-only packet is
`evidence/s4-tx1-concrete-ten-field-results-root-v4-20261021`.

`S4ConcreteConstructorBoundsV1.source_final_len_total_and_bounded`
(namespace `AspisR1S4ConcreteConstructorBoundsV1`) reuses verbatim the small
symbolic checked-multiplication/shift proofs from Tx1FinalLenBoundV8. It
proves totality and exact final lengths256/64/64 by variant, hence length
at most256, for the concrete current-carrier constructor leaf. This is
independent of allocator or constructor success. Focused compile: exit0,
5.688s,peak process RSS2,220,572,672 bytes,zero swaps,standard axioms.
Packet: `evidence/s4-concrete-constructor-bounds-root-v1-20261021`.

## Candidate loops and the current query source owner

`evidence/s4-candidate-loop-field-transport-v1-20261021` proves same-output
transport for successful candidate ten/twelve-query loops to the selected
original-dot model, then derives the existing field-result witnesses. These
first corollaries enumerate the transported model calls; a stronger version
retaining each actually reached candidate call is being developed. No
independent successful old loop is assumed.

A comparison initially used the historical c8ea query source cut, which
differs from current Rust after its first four statements. That was not the
selected theorem owner. The selected Stage2ContinuationQueryAdvance and
Stage2ContinuationQueryLoop owners already use the current unrolled traces,
owned accumulator/pending and pair result. Existing stage2b source pins
identify candidate.rs5164975d, identical to current production. The builder
packet now retains the exact current owners, generated bodies, typed callee
parameterization checks and explicit historical-prefix classification. The
historical comparison does not reopen the current query suffix. Extraction
trust and concrete child binding remain explicit.

The upstream preparation issue is precise: the existing
S4PreparedScratchClaimPowersV1 theorem already derives canonical gamma and
same-array ClaimPowers from one successful PreparedScratchModel run. There
is not yet an accepted binding from the current caller's abstract prepare
slot to that complete run. hprepareBinding is retained; a model powers
theorem is not being relabeled as source dispatcher closure.

The candidate's direct Q::from_limbs validation-to-parser join is now the
next local backend target. Candidate adoption, the original from_fn source
boundary, upstream concrete driver binding and final artifact/release replay
remain unresolved. S4 and the implementation-linked100-bit target remain
open.

## Same caller to actual candidate query witnesses

`AspisR1S4CandidateTx1ActualFieldsRootV1.candidate_source_tx1_success_ten_actual_field_results`
is green. It starts from one successful tx1 in the source-installed candidate
caller, derives split10 and constructor cursor0 from that same execution,
and obtains all ten actually reached candidate query calls with field-result
evidence at the same accumulator and coefficient array. It does not assume
a successful loop, a starting cursor, or independently successful old-model
queries. The full arithmetic backend and constructor leaf operations are
concrete. Scanner and same-run preparation/ClaimPowers bindings remain
explicit upstream contracts.

The composition reuses
`evidence/s4-candidate-loop-actual-calls-v1-20261021` and
`evidence/s4-candidate-caller-prepared-root-v1-20261021`. The accepted
focused compile took16.801s,peak process RSS3,938,385,920 bytes,zero swaps,
standard axioms. Source-only packet:
`evidence/s4-candidate-tx1-actual-fields-root-v1-20261021`. A failed first
application needed an explicit function-equality transport through the
already opaque loop; its source and diagnostics are retained, and no
resource override was used.

The concrete QueryOps builder evidence now checks the complete retained
provenance chain: current candidate.rs5164975d as Charon input, emitted
LLBC4c36344e as Aeneas input, and final generated Funsb3aa665d as the source
of the checked typed-callee parameterization. The existing generation
checks were rerun; unchanged Lean extraction/dependency jobs were not.

This is progress on the unadopted candidate path, not frozen-implementation
S4 closure. The local validation-to-parser join, actual source/driver
installation of upstream bindings, candidate adoption/final artifact pins
and the final coherent release replay remain open. The 100-bit goal is
not yet established.

## Actual callback output meaning and validation scope correction

`AspisR1FastDotsV10CallbackOutputFieldResultsV1.concrete_candidate_dots_success_has_endpoint_fields`
identifies the actual candidate callback's returned array with the canonical
four-value array and its four literal field results. It consumes the existing
fullArrayToCurrent g = claimArrayToFast claimPowers identity; the additional
V10 input map is derived, not supplied. No successful old/P6 callback is
assumed. Focused compile: exit0,29.682s,peak process RSS3,914,432,512 bytes,
zero swaps,standard axioms. Packet:
`evidence/s4-v10-callback-output-field-results-v1-20261021`.

Correction to the validation subtask: private fast_pairing checked_q accepts
a QM31 value and calls Q::from_limbs(limbs_of(k)); limbs_of projects its four
existing field coordinates. It does not call U32::from_le_bytes. A separate
green byte-codec validation/parser lemma does not establish this actual
child dispatch, and its missing resource receipt prevents a release claim.
It remains candidate-only. The active proof target is the exact candidate
checked_q/limbs_of path on the current scalar carrier, reusing the retained
four-comparison validation theorem and canonical coordinate bounds.
This supersedes treating a byte-decoder seam as the critical checked_q gap.

## Direct returned-array evidence in both query segments

`AspisR1S4CandidateTx1OutputFieldsRootV1.candidate_source_tx1_success_ten_output_field_results`
now retains one shared canonical gamma/ClaimPowers vector and all ten reached
candidate calls. Each `CandidateQueryFieldEvidence` explicitly includes the
actual candidate dots-callback success equation, equality of that returned
array with the four canonical field values, and their four literal field
results. This strengthens the earlier old-model QueryFieldEvidence consumer.
The first single-query draft used its callback equation in the proof but
omitted that equation from its exported existential; statement review caught
and corrected this before the end-to-end theorem was compiled.

The focused tx1 compile passed in22.783s,peak process RSS3,958,915,072 bytes,
zero swaps,standard axioms. Packet:
`evidence/s4-candidate-tx1-output-fields-root-v1-20261021`. Single-query
source composition and its corrected evidence predicate are retained in
`evidence/s4-v10-candidate-query-field-evidence-v1-20261021`.

The settlement-side prefix analogue is
`AspisR1S4Tx2ResumeTwelveActualCallsV1.resume_model_candidate_twelve_actual_field_evidence`,
retained in `evidence/s4-tx2-resume-twelve-field-evidence-v2-20261021`. It
invokes the selected resumeWithOps, derives next=10 from the following
rejecting guard, and obtains all twelve actual candidate calls with direct
returned-array field evidence, from the same source-prefix success. It
retains ResumeOps, strict scan, prepared gamma/P6-powers contracts and the
documented suffix operations. This is a source-installed resume/prefix
composition, not yet full tx2_common/tx2_authenticated refinement. Focused
compile:22.330s,peak RSS4,001,775,616 bytes,zero swaps,standard axioms.

The checked-Q candidate-to-QRaw full-Result bridge was already proved in
commit19eeb1bb3 (`evidence/s4-checked-q-push-bridge-v1-20261021`). Reusing
that stronger result avoids duplicating its validation/wrapper proof. The
new concrete-record projection installs it directly at ebyKPush; the
additional parser-output coordinate theorem is supplementary. Its launch
revision is recovered from reflog/object timing, not captured at launch, as
recorded in `evidence/s4-checked-q-parser-output-v1-20261021`.

Correction to another potential false gap: the actual V10 helper and its
head body do not invoke arrayFromFnP6. They use literal eight-coordinate
updates and Array.make8, with registered Aeneas Range/StepBy models. The
P6 array slot belongs to the original reference side, not the actual V10
execution. Explicit dead-slot lemmas for arrayFromFn and wideLimbCount are
being checked to make this distinction robust. The frozen original's Std
from_fn source boundary remains open; the candidate remains unadopted.

Input provenance from concrete preparation/scanner belongs upstream S1/S2;
it must be composed for the global theorem, but is distinct from an open S4
arithmetic law. Candidate adoption also still conflicts with the historical
B1 fixture CU criterion. The implementation-linked100-bit target is not
yet established.

## Candidate execution no longer requires a from_fn interpretation

`AspisR1S4V10NoFromFnKernelRootV1.no_from_fn_outer_eq` proves full-Result
equality after replacing both the unused arrayFromFn slot and the unused
wideLimbCount slot with divergence.
`no_from_fn_outer_total_and_field_results_from_scan` nevertheless proves
complete candidate execution, mapped canonical values and all four field
results on the scanner/ClaimPowers input contract.
`no_from_fn_dots_eq_concrete` identifies that no-fromFn callback with the
concrete candidate query callback for every input. Thus no Rust-to-custom-P6
from_fn assumption is needed for actual V10 execution; P6 is used only as a
mathematical reference inside the proof. The original frozen implementation
still has that distinct source boundary.

Focused compile: exit0,35.423s,peak process RSS3,896,279,040 bytes,zero swaps,
standard axioms, captured launch revision57ca9c452. Packet:
`evidence/s4-v10-no-fromfn-kernel-root-v1-20261021`. The supporting all-result
slot proofs are retained in
`evidence/s4-v10-dead-arrayfromfn-slot-v1-20261021` and
`evidence/s4-v10-wide-limb-count-irrelevance-v1-20261021`. The concrete
checked-Q push record projection is retained in
`evidence/s4-concrete-candidate-push-slot-v1-20261021`; it reuses the already
committed full-result candidate-to-QRaw theorem.

The actual returned Stage2 FullWide array now also carries its eight explicit
raw-coordinate bounds, derived from the same CandidateQueryFieldEvidence
without new scalar premises, in
`evidence/s4-candidate-query-fullwide-bounds-v1-20261021`.

NUC standing-runner-v2 evidence was read and archived without new builds or
regression reruns. Its thirty command receipts all exit0 against artifact
40dc7574, under capped zero-swap scopes. Six retained fixture reports confirm
maxima1,210,100/1,189,265 CU and the actual1,400,000 transaction limit.
`evidence/s4-combined-standing-retained-v2-20261021` contains the whitelisted
metadata/public fixture evidence and output-log hashes; no keys, proofs or
program binaries were copied or deleted. The old exit127 runner attempt is
not accepted evidence. Fixture success and cost measurements do not establish
an all-input cost bound or the cryptographic soundness theorem.

`design/S4-NEXT-FREEZE-RECOMMENDATION-20261021.md` makes the source tradeoff
concrete: the proof-friendly candidate avoids the custom from_fn gap and
fits the measured transaction budget, but fails the historical B1 criterion.
It remains unadopted; no security criterion or performance gate was silently
relaxed. Complete source/driver instances, remaining other-cone obligations
and final release replay/artifact binding still prevent a100-bit claim.

## Complete candidate query equality and ten-query raw bounds

The selected execution model now has full-Result equality of its QueryOps
record, complete query and complete query loop when the two unused from_fn
slots diverge. There are no acceptance, scanner or canonicality premises in
these equality statements. This extends the already proved callback equality;
it does not assert source adoption. Packet:
`evidence/s4-v10-no-fromfn-queryops-equality-v1-20261021`.
Focused compile: exit0,9.551s,peak process RSS4,008,951,808 bytes,zero swaps,
standard axioms, captured launch revision3af931da4.

An initial producer lookup incorrectly associated the loop object with the
earlier v1 receipt (source hash beginning6eec6a3f). The exact selected object
20a8d684 is instead produced by the existing successful
`evidence/stage2-continuation-20261020/proofs/query-loop-v2/receipt.json`:
its source hash c398ba41 equals the current tracked loop source. The v1/v2
diff changes only the private `actual_body` proof script, not the definitions.
The packet now pins the correct v2 source/object receipt and verifies the
identity. This resolves that specific provenance issue without any rebuild;
it does not discharge other transitive source/driver bindings.

`candidate_source_tx1_success_ten_fullwide_coordinate_bounds` composes the
ten-query caller result with the existing coordinate consumer. For every one
of the same ten actual calls it retains the successful opening and dots
callback and proves all eight coordinate bounds on that exact returned
array. No independent callback success or scalar bound was added. The
concrete scan/preparation bindings and non-S4 operations remain explicit.
Packet: `evidence/s4-candidate-tx1-output-fullwide-bounds-v1-20261021`.
Focused compile: exit0,8.375s,peak RSS3,964,796,928 bytes,zero swaps,standard
axioms, captured launch revision3af931da4.

Only source/receipt packet checks were rerun for integration. No unchanged
Lean compilation, runtime suite, or package replay was repeated. The full
settlement caller connection and coherent final closure remain open; neither
S4 nor the implementation-linked100-bit target is declared closed.

The twelve-query resume-prefix analogue is also checked in
`evidence/s4-tx2-output-fullwide-bounds-v1-20261021`:
`tx2_after_resume_candidate_twelve_fullwide_coordinate_bounds` preserves each
same query/opening/dots success and bounds that exact returned array. It adds
no independent success or coordinate premise. Focused compile:exit0,4.008s,
peak RSS4,057,530,368 bytes,zero swaps,standard axioms. Its resume-prefix
premise is still a model boundary, not full Rust tx2_common acceptance; a
separate exact-body caller composition is in progress.

`evidence/s4-tx2-authenticated-wrapper-cut-v1-20261021` proves that accepted
execution of the authenticated wrapper operation cut reaches the same
tx2_common call with unchanged public/proof/checkpoint/hash/observer
arguments, after successful parsing and the Parsed mark. Its checker compares
the complete pinned Rust/generated wrapper bodies and the complete cut body
under an explicit callee/type substitution map; this replaces ordered-marker
checks as the source-body evidence. Concrete operation implementations still
require their own bindings. Focused compile:exit0,12.342s,peak process
RSS2,242,428,928 bytes,zero swaps,standard axioms.

The full settlement cut still requires canonical prepared gamma and the
same-proof strict scan. Existing concrete decoder canonicality can supply the
first only after its reader operation is bound to ResumeOps.readE and the
same successful resume output. The second comes from prior tx1 and the
authenticated checkpoint/proof context: tx2_common contains no strict scanner.
Neither condition may be silently inferred from arbitrary ResumeOps or from
tx2 success alone. The concrete-reader/resume connection is being proved;
the scanner/checkpoint context remains an upstream integration boundary.

## Complete emitted settlement body reaches the twelve S4 results

The complete emitted tx2_common body, including every residual branch and
the inline post-query suffix, is now copied into a typed operation cut and
compared token-for-token with its pinned generated body under a declared
callee/constant substitution map. This supersedes the earlier ordered-marker
evidence for the hand-cut resume/prefix/complete wrapper. No arbitrary
`complete` suffix port occurs in this new body. Its success-inversion theorem
derives the same successful resume, split cursor, powers array, geometry,
pending state and actual selected query-loop success. Packet:
`evidence/s4-tx2-full-source-owned-cut-v1-20261021`.
Focused compile:exit0,7.053s,peak RSS4,095,246,336 bytes,zero swaps,standard
axioms, captured launch revision8b9811238.

`AspisR1S4FullTx2CandidateFieldsRootV1.full_tx2_source_cut_success_twelve_actual_fields`
installs split10, the existing source-powers interface and the actual
candidate query callback in that complete body. From one successful common
caller execution it derives all twelve actual query calls and, for each,
CandidateQueryFieldEvidence plus the successful opening/dots callback and
eight coordinate bounds on that exact returned array. The same source
powers result supplies ClaimPowers and its array correspondence. The theorem
does not assume an independently successful prefix, query loop, initial
cursor or powers call. The wrapper theorem reaches that same complete body
from authenticated-wrapper success. Packet:
`evidence/s4-full-tx2-candidate-fields-root-v1-20261021`.
Focused compile:exit0,6.777s,peak process RSS4,060,282,880 bytes,zero swaps,
standard axioms, captured launch revision8b9811238.

The remaining contracts are not hidden: canonical gamma from the same
resume and prior same-proof strict scan are explicit; non-S4 Ops are still
operation boundaries, and S1 must bind the chosen powers implementation to
the installed source-powers interface. Exact body preservation does not
discharge concrete child-operation semantics. The candidate remains
unadopted and the B1 performance failure is unchanged. These results remove
the synthetic-prefix caller premise but do not close frozen-source S4 or
the implementation-linked100-bit theorem.

## Reuse for the concrete resume decoder

The complete resume output projection already exists in
`lean/OraclePortCkptAbiSourceFields.lean`: `successful_fields` supplies a
`Fields` witness whose `gammaRead` is the exact successful first readE call
returning the same Prepared.gamma. Its selected resume body matches the
current source. A new handwritten inversion of the long resume suffix is
therefore unnecessary; the next composition reuses this owner.

`evidence/s4-wide-exact-decoder-source-binding-v1-20261021` checks that the
current full wide_exact.rs file equals the retained source snapshot, that its
from_le_bytes and from_limbs fragments match the admitted record-parser
fragments, and that the generated method bodies match the retained record,
view and current Echeck owners. Existing byte-decoder canonicality consumes
the exact limb-validation theorem. This is source/body-identity evidence,
not a new translation-soundness theorem; its checker passes without rerunning
unchanged Lean proofs.

The fieldwise eight-bound-to-ClaimCanonical bridge has passed its focused
predecessor check with no axioms (exit0,6.942s,peak process
RSS4,041,883,648 bytes,zero swaps). The concrete Reader.e operation adapter
and successful-resume composition remain in progress; the new full settlement
consumer will only be accepted after those exact owners compile and compose.
No template decoder axiom is being accepted as a canonicality law.

## Canonical gamma is now derived from the same successful resume

`evidence/s4-reader-e-current-canonical-v2-20261021` installs the concrete
strict byte decoder in the complete emitted Reader.e operation body. Its
dependent raw-read argument has the exact ResumeOps signature. Success of
that body implies all eight current-carrier coordinate bounds, without any
decoder-success or canonicality-law premise. It directly reuses
`ExtractedRecordByteCanonicality.slice_success`; no older Reader carrier is
imported. The complete source-body checker permits only the documented
raw/decoder/Option callee substitutions. Focused compile:exit0,9.819s,peak
RSS2,256,715,776 bytes,zero swaps,standard axioms.

`evidence/s4-resume-gamma-actual-canonical-v1-20261021` then reuses the existing
complete `successful_fields` theorem and its exact `gammaRead` witness.
Installing that concrete Reader.e in ResumeOps proves the eight bounds for
the gamma returned by the same successful resume. The selected v3 receipt
is against the direct-byte-proof parent:exit0,2.862s,peak RSS2,244,476,928
bytes,zero swaps,standard axioms. The earlier isolated wrapper proof is not
used by the composed current S4 import.

`AspisR1S4ConcreteResumeTwelveFieldsRootV2.full_tx2_concrete_reader_twelve_actual_fields`
composes this result with the complete settlement-body theorem. The previous
`hcanonical : ∀ p a, same_resume_success → Canonical gamma` premise is gone.
The new concrete operation record fixes readE to the strict source adapter;
its canonicality follows from execution. From the one accepted full body it
retains all twelve actual queries, same-array field equations and coordinate
bounds. The only additional input proposition is the prior same-proof strict
scan; other raw/non-S4 operations and the S1 powers implementation remain
explicit source boundaries. Packet:
`evidence/s4-concrete-resume-twelve-fields-root-v2-20261021`.
Focused compile:exit0,11.464s,peak RSS4,053,286,912 bytes,zero swaps,standard
axioms; its fieldwise canonicality helper has no axioms.

Two integration failures are retained as diagnostics: a partial canonical
cache shadowed unrelated Mathlib modules, and the older Reader carrier
collided with current FinishRelation.Types. The accepted profile selects
only the needed project cache owners and the direct byte canonicality proof.
No unchanged full regression or package build was run. No production source,
security parameter or candidate-adoption decision changed.

The next S4 arithmetic join identifies these four returned dot values with
the matching four width-29 first-fold inputs of dV_frozen2. The shared byte
interface is the exact 608-byte prefix equalling encodeC1++encodeC2, followed
by the 26 M31 and three QM31 lane projections and same-g power equations.
Merkle authentication and prior-tx checkpoint context stay with their named
upstream owners; source adoption/B1 and the other whole-cone joins remain
open. The implementation-linked100-bit target is not yet established.


## Canonical block splitting and decoder completeness, 2026-10-22

`evidence/s4-canonical-fixed-width-completeness-v1-20261022` proves
`S4CanonicalBlocksV1.canonical_split_blocks`: a canonical byte list remains
canonical in both pieces at any four-byte-aligned split, including short
inputs. It also proves structural fixed-width decoder completeness for any
block decoder whose completeness and predicate-preserving split are supplied.
The latter generic theorem retains those two contracts; it does not assert
that the concrete M31/QM31 decoder contracts have already been discharged.
These lemmas let the opening proof derive successful C1/C2 decoding from the
prior strict scan rather than assume an encoded opening identity.

Focused target exit0,26.075s,peak process RSS3,597,565,952 bytes,zero swaps;
both axiom reports contain only propext and Quot.sound. The rejected first
attempt and exact source are retained: multiplication by n+1 needed explicit
`Nat.mul_succ` normalization before linear arithmetic. No full replay or
production source change occurred. The next concrete target is strict M31
canonical-byte completeness, followed by QM31 and the 608-byte instantiation.
S4 source adoption and the implementation-linked100-bit target remain open.
