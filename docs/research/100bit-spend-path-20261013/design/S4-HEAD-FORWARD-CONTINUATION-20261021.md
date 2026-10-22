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


## Concrete codec and 608-byte opening completeness, 2026-10-22

The generic decoder contracts now have concrete instances:
`evidence/s4-canonical-m31-completeness-v1-20261022` proves successful strict
exact-M31 decoding for every canonical four-byte list (exit0,23.457s,peak
RSS3,628,089,344 bytes,zero swaps). The exact-QM31 counterpart in
`evidence/s4-canonical-qm31-completeness-v1-20261022` proves the same for a
canonical sixteen-byte list, with an exact list-window theorem for each
of its four limbs (exit0,6.702s,peak RSS3,630,710,784 bytes,zero swaps).
These reuse the retained codecs and endian theorem; there is no new decoder
law axiom or assumed successful decoding. Reports contain standard axioms.

`evidence/s4-canonical-opening-completeness-v1-20261022` instantiates the
structural theorem for C1's 26 M31 plus one QM31 slot, C2's two-QM31 slot,
and the four slots in each leaf. Its final theorem
`S4CanonicalOpeningV1.canonical_opening_decode_exists` takes only
`bs.length = 608` and canonicality. It derives both successful decodes of
that same list's 480/128-byte pieces and the literal identity
`bs = encodeC1 c1 ++ encodeC2 c2`. Successful decode and that desired byte
identity are conclusions, not premises. Focused compile exit0,7.822s,
peak RSS3,626,614,784 bytes,zero swaps; six standard-axiom reports.

The bytes-to-typed-leaf existence gap is closed at the mathematical codec
boundary. Same-source-array/strict-scan application and the decoded leaves'
global recovered-word binding must still compose with the actual caller;
the four-dot field equality and candidate-adoption boundaries are unchanged.
These local claims do not close S4 or establish the100-bit target.


## The same scanned source array now supplies the encoded opening identity

`evidence/s4-scanned-source-opening-decode-v1-20261022` composes the existing
strict-scan/opening canonicality owners with the new codec completeness.
`S4ScannedOpeningDecodeV1.scanned_opening_decode` takes the same scanner
success, exact source opening read, index <22, proof length57607 and
`a.val = q.val.slice 0 608`. It returns successful C1/C2 decodes of the same
actual array's raw-byte prefix and suffix, plus
`a.val.map rawByte = encodeC1 c1 ++ encodeC2 c2`.
There is no separate canonicality, decoder-success or desired byte-identity
premise. The existing scanner proofs were reused without replay. Focused
consumer exit0,14.275s,peak process RSS3,981,492,224 bytes,zero swaps,
standard axioms. Exact source/compiled import hashes are in the packet.

Thus the common byte interface for the head/tail projection workers is now
derived from execution's scanner and opening read. Its identification with
the global recovered Merkle words and the final width29 arithmetic join are
still required; no commitment-source closure or candidate adoption is implied.


## Same returned coefficients now have their semantic gamma-power equations

`evidence/s4-same-caller-powers-semantic-v1-20261022` reuses the existing
`powers_total_exact` theorem, identifies its output with the same successful
Claim powers call, and transports its values through `claimArrayToFast`.
`successful_powers_exact` gives every index's decoded coefficient as
`Concrete.decode gamma ^ index`; `caller_powers_exact` applies this to the
same caller array identity. The fieldwise decode identity is definitionally
proved, but all three axiom reports include standard axioms from their
imported definitions. Focused exit0,7.724s,peak RSS3,270,443,008 bytes,zero
swaps. No new mathematical power-law contract is assumed.

`evidence/s4-actual-resume-powers-semantic-v1-20261022` then removes the
independent gamma-canonicality and Claim-array premises at the concrete
settlement operation boundary. From the same successful concrete-reader
resume returning Prepared p and the same successful sourceP6WeightsPowers
call returning g, `S4ResumedPowersSemanticV1.same_resume_source_powers_exact`
derives every decoded entry of `fullArrayToCurrent g` equals
`Concrete.decode (stage2ToClaim p.gamma) ^ index`. It reuses the concrete
reader canonicality and source-to-Claim array identity already established
by the complete settlement consumer. There is no independent successful
Claim call, fresh coefficient array or assumed coefficient equation.
Focused exit0,26.150s,peak RSS3,991,224,320 bytes,zero swaps,standard axioms.

The remaining source powers installation obligation and non-S4 operation
boundaries are not discharged here. The arithmetic lane joins, recovered
model word binding and candidate adoption remain open, as does the full
implementation-linked100-bit target.


## Same candidate query and twelve settlement openings are now typed

`evidence/s4-same-query-typed-opening-v1-20261022` preserves every witness
of CandidateQueryFieldEvidence: the actual indexed query and opening read,
actual dots callback result, same Current-carrier output array and four
LiteralFieldResult equations. It derives successful C1/C2 decodes and exact
encoded-byte identity for that same arrayQ. No independent query-index bound,
proof length, canonicality or successful decoder is assumed; the index bound
comes from the actual array index success and length from the same strict scan.
Focused exit0,11.487s,peak RSS4,052,025,344 bytes,zero swaps; three standard
axiom reports. Predicate enrichment is proved, not merely assumed in a new
structure; existing query evidence and prior same-proof scan remain premises.

`evidence/s4-tx2-twelve-typed-openings-v1-20261022` composes that enrichment
with the complete settlement source-cut success theorem. Each of the same
twelve actual calls now carries the same four output field equations and
typed decoded opening. All former source-cut, raw/non-S4 operation boundaries,
prior scan context and candidate adoption limitations remain explicit; no
new decoder or desired encoded-byte premise is added. Focused exit0,7.261s,
peak RSS4,053,975,040 bytes,zero swaps,standard axioms. The lane embeddings,
width29 equality and global recovered-word binding remain open.


## Ten first-stage queries now retain typed decoded openings too

`evidence/s4-tx1-ten-typed-openings-v1-20261022` composes the same-query
encoding result with the actual reached first-stage calls. Its theorem
`S4Tx1TypedOpeningsV1.candidate_source_tx1_success_ten_typed_openings`
retains the existing scan/prepare source bindings and all same-array powers
facts, and upgrades each of the same ten actual query results to typed
opening evidence. It adds no independent successful decode, desired byte
identity, index-bound or proof-length premise. This and the already proved
twelve-query settlement consumer cover all22 calls at this boundary.

Focused exit0,42.015s,peak process RSS3,762,700,288 bytes,zero swaps,
standard axioms, launch revision6a86aa5dc99079058c80b9ad02752c4367b2db1c.
The first attempt only lacked the already compiled first-stage prepared-caller
module in the selected settlement cache; its diagnostic is retained. The
accepted environment appends the previous successful ten-query profile to
supply missing owners. No dependency build, whole-manifest replay or Rust
source change was run. Caller source bindings, final arithmetic/model join,
coherent release replay and candidate adoption remain open.


## Local decoded opening to existing recovered-word projection

`evidence/s4-decoded-opening-recovered-word-v1-20261022` proves
`S4RecoveredOpeningWordV1.decoded_pair_matches_recovered_word`: given the
same successful C1/C2 decodes and the primitive packed byte-map facts at
`queryLeaf i`, every coordinate of the existing TypedRecoveredWords.word
at i equals the corresponding local LiteralTypedWords.word coordinate of
those decoded leaves at `querySlot i`. No global word equality is assumed.
The canonical608 variant derives the decodes and encoded-byte identity
before proving that same all29-coordinate equality. Existing word/decoder
projections are reused; there is no new commitment model.

This closes the representation projection conditional on the two named
byte-map entries. It DOES NOT prove the actual Merkle/caller authentication
supplies those entries: that concrete recovered-map correspondence remains
an upstream obligation. Query leaf/slot geometry and the width29 field-value
join also still need composition. Focused exit0,21.784s,peak process
RSS3,578,331,136 bytes,zero swaps; both reports contain standard axioms.
No Rust source change or candidate adoption occurred.


## The typed opening slot is the existing first-fold input position

`evidence/s4-opening-first-fold-geometry-v1-20261022` proves that the existing
initial childIndex u slot has TypedRecoveredWords.queryLeaf=u and
querySlot=slot. Using those representation identities,
`S4FirstFoldOpeningGeometryV1.decoded_opening_first_fold_inputs` identifies
each recovered lane's existing FirstFold.fibre value with the same decoded
local C1/C2 slot. Primitive recovered-byte map facts and the exact decodes
remain explicit; authentication is not assumed solved by this projection.

`batch_value_is_first_fold_fibre` then identifies width29Batch of these29
per-lane first-fold values with FirstFold.fibre of the existing
TwoFoldExtraction.batchedWord. This generic identity unfolds the existing
model definitions and does not introduce a new folding model, prove a fold
equation or assert the source dot output equals that batch. It fixes the
precise target for the arithmetic join. Focused exit0,23.614s,peak process
RSS3,578,331,136 bytes,zero swaps; four standard-axiom reports. Source
query geometry correspondence, arithmetic join and coherent release replay
remain required. No production change or candidate adoption occurred.


## Actual tail coefficient reads have their source-indexed gamma powers

`evidence/s4-tail-source-coefficient-powers-v1-20261022` proves
`S4TailCoefficientPowersV1.index_success_power`: an actual successful
Array.index_usize read from the same29-entry powers array returns a value
whose decode equals gamma to that exact index. The source read supplies its
own index bound and value identity; no independent successful read or desired
returned-value equation is assumed.

`tail_trace_coefficient_powers` reuses the existing SourceMeaning projection
of the actual checked tail-body trace. For every retained contribution c,
it derives decoded coefficient = gamma^(26+c.term.val), using the same-array
all29 power equations already supplied by the concrete resume/source-powers
consumer. No extra tail term bound is needed for this step: the actual array
read itself supplies the valid coefficient index. The general index lemma
also covers the actual coefficient28 read. Scalar parser equality remains
the tail worker's separate obligation.

Focused exit0,6.695s,peak process RSS3,239,280,640 bytes,zero swaps; four
standard-axiom reports. The rejected first attempt is retained: an ambiguous
local Range alias and a scalar-literal simplification needed correction.
No whole replay or source adoption occurred. The full arithmetic/model join
and implementation-linked100-bit target remain open.


## Width29 algebra and full26 head projection have checked owners

`evidence/s4-width29-literal-join-d18-v1-20261022` proves the complete
algebraic26+3 join from an existing LiteralFieldResult. Its hhead, hwide28,
hfirst and htail value-identification premises remain explicit; follow-on
composition must discharge them from the same bytes and actual trace.
The proof reuses Fin.sum_univ_add instead of a custom range sum proof.
Focused exit0,8.986s,peak RSS3,670,228,992 bytes,zero swaps,standard axioms.

The packet records the unchanged V6 source's isolated owner rebuild and
selected843-module AspisFormal overlay. The previous instantiated sum had
a missing SimplexCategory instance and failed rfl; the new owner passes
unfold/rfl and the exact existing finite-sum split. This is a local compiled
owner repair, not adoption of a new protocol source or a coherent final
release replay. The historical/global owner remains untouched.

`evidence/s4-head-codec-projection-v1-20261022` records the source byte-to-M31
and head parser embedding facts with standard-axiom audit. Its old head-v13
original command/LEAN_PATH was not retained; that provenance limitation is
explicit and it must not be treated as a final formal-release producer until
coherent receipt repair/replay. Exact-name C1 slice receipt repair is recorded.
`evidence/s4-head-fin26-codec-wrapper-v1-20261022` adds a newly recorded focused
consumer: from shared hbytes and all29 same-g power equations it derives
all26 exact head terms, without separate cell/read premises. Focused exit0,
8.233s,peak RSS3,706,109,952 bytes,zero swaps,standard axioms.

## The actual returned source array preserves decoded field values

`evidence/s4-same-returned-array-semantic-transport-v1-20261022` proves the
fieldwise Current-to-Full map preserves all eight coordinates and decoded
values, for arbitrary raw inputs without a canonicality premise.
`S4ReturnedValueTransportV1.same_returned_array_decode` uses the exact array
identity already retained by candidate query evidence; it transports the
Current-carrier decoded list to that actual returned Full-carrier list.
It does not prove their arithmetic value or any hash/oracle trace equality.
Focused exit0,13.042s,peak RSS3,976,593,408 bytes,zero swaps; three standard
axiom reports. The concrete one-slot arithmetic join, four-slot lift and
actual query/model composition remain in flight; source adoption and the
implementation-linked100-bit target are still open.


## Trace member witnesses and exact two-term bounds

`evidence/s4-actual-tail-trace-member-witness-v1-20261022` derives each
contribution's original same-step InputWitness by structural induction on
RunTrace. For the actual source range0..2, the retained exact term-index
sequence also gives every contribution's term <2. The scalar-byte worker
can therefore select its actual C2 Fin2 lane and invoke its same-step parser
proof, without assuming an independently successful step or term bound.
Focused exit0,3.684s,peak process RSS2,242,199,552 bytes,zero swaps; both
reports have standard axioms. Rejected first attempt is retained (the
membership simplifier needed to eliminate the final empty-list case).

A source/model boundary remains explicit for the ten-query first-stage
consumer: its existing prepare binding supplies a canonical gamma and same
powers array but the generic statement does not additionally assert that
this gamma is the model's transcript challenge. The actual S1 preparation
and sampler owners must supply that correspondence. The twelve-query
concrete resume consumer instead derives powers for the exact Prepared.gamma
returned by that resume; transcript/sampler correspondence remains outside
these local arithmetic projections. None of the local gamma-parameterized
results alone establishes the implementation-linked100-bit target.


## Concrete callback arithmetic and four-slot/model transport, October 22

The concrete width-29 kernel now derives the 26 head values, the C1 tail
parser value, both C2 parser values and all coefficient reads from the same
LiteralFieldResult, the common encoded opening and the same 29 powers.
`s4-concrete-width29-kernel-d18-v1-20261022` retains the exact theorem
`literal_field_result_concrete_width29`: no per-term scalar or desired-output
equality is supplied. Its focused compile exited 0 in 7.694s, peak RSS
4,073,619,456 bytes, no swap, standard axioms. Launch HEAD was not captured
for that job; the packet explicitly records the missing launch pin rather
than substituting packaging HEAD. This is not final release evidence.

`s4-four-slot-current-array-semantics-v1-20261022` lifts those concrete
results to the same four-element Current returned array (exit 0, 6.73s,
peak RSS 4,065,329,152 bytes, no swap, standard axioms).
`s4-tail-parser-witness-embedding-v3-20261022` retains the unique-module
parser embeddings and the term-index-linked actual tail trace. Rejected
same-name/self-import and weaker predecessor attempts remain diagnostics.
The v1/v2 parser packet assemblies are not accepted.

`s4-local-batch-model-transport-v1-20261022` proves the local batches equal
the first-fold inputs of the existing TypedRecoveredWords.word, given the
primitive packed-map byte identities and successful C1/C2 decodes for that
same opening. No unconstrained replacement word is introduced (exit 0,
4.293s, peak RSS 3,633,561,600 bytes, no swap, standard axioms).
All four packet checkers passed during primary review.

These results remove local arithmetic/parser premises. The primitive
commitment-authentication identities, source-candidate adoption or frozen
from_fn correspondence, full caller composition, stage-1 transcript-gamma
binding and final coherent dependency replay remain open. S4 and the
implementation-linked 100-bit target are not declared closed.


## Same Current returned array reaches recovered-word model inputs

`s4-current-array-model-inputs-v1-20261022` composes the concrete four-slot
result with the existing recovered-word transport. The theorem
`AspisR1.S4CurrentArrayModelInputsV1.same_current_array_is_model_input`
identifies the decoding of that exact returned Current array with the four
first-fold inputs of TypedRecoveredWords.word under the actual field
embeddings. The same four callback results and the same opening are retained;
no desired returned-value equation is assumed. Primitive packed-map byte
identities and same-opening decoder facts remain explicit.

Focused exit 0, 7.423s, peak RSS 4,064,755,712 bytes, swap 0, standard axioms.
Two preceding setup failures (missing selected kernel root, then incomplete
model import closure) are retained; no source-theorem change was required.
The packet checker passed. No whole-caller or final source-freeze closure is
claimed by this mathematical/source-carrier composition.


## Actual callback values and ten-query stage-1 consumer

`s4-query-returned-local-batches-v1-20261022` establishes
`AspisR1S4QueryReturnedSemanticsV1.typed_opening_returned_local_batches`.
The same typed opening witness, same successful Claim powers call and
canonical gamma now imply the actual returned Full array decodes to the
four local width29 batch values. The result retains the original reached
index, source opening, concrete dots success, Current-to-Full array identity,
all four callback witnesses and both successful typed decodes. No independent
dots success or desired value equation is assumed. Focused exit 0, 5.977s,
peak RSS 4,064,673,792 bytes, no swap, standard axioms. A rejected ambiguous
namespace attempt is retained; selective opens fixed it without changing
the theorem statement.

`s4-tx1-ten-returned-local-batches-v1-20261022` composes that result with
the actual candidate source tx1 cut: every one of its ten reached callbacks
has the returned-array semantic result. Its exact original caller success
and per-query success witnesses remain. Focused exit 0, 6.237s, peak RSS
4,050,108,416 bytes, no swap, standard axioms; both packet checkers passed.

The stage-1 preparation binding still supplies an existential canonical
gamma and same powers array; this theorem does not newly identify that gamma
with a model transcript challenge. Scan/preparation bindings, non-S4
operation boundaries, primitive commitment authentication, candidate source
adoption or frozen from_fn refinement, and final coherent replay remain
open. This closes the returned-value arithmetic join along the accepted
candidate tx1 cut, not the entire frozen S4 cone or the 100-bit target.


## Twelve settlement callbacks return the intended local batch values

`s4-tx2-twelve-returned-local-batches-d18-v1-20261022` establishes
`AspisR1S4Tx2TwelveReturnedLocalBatchesV1.full_tx2_twelve_actual_returned_local_batches`.
It consumes the original same-proof strict scan and complete candidate tx2
source-cut success. The exact reached resume supplies gamma canonicality;
the exact source powers call supplies all 29 decoded powers. For every one
of the twelve actual reached query calls, the result retains its success
and identifies its actual returned Full array with the four width29 local
batches for its own same decoded opening and resumed gamma. No independent
callback success, parser output, desired output equation or gamma
canonicality premise was added.

Focused exit 0, 7.70s, peak RSS 4,063,887,360 bytes, no swap; named axioms
are standard-only. The primary packet checker passed. Its runner did not
capture launch Git revision; this is explicitly UNKNOWN_NOT_CAPTURED and
not substituted by packaging HEAD. The result therefore is focused local
source-cut evidence, not a final release replay.

Together with the ten-query result, the arithmetic return-value join is
proved on both candidate source cuts. Non-S4 source operations, prior scan
binding, commitment authentication, stage-1 transcript gamma correspondence,
frozen from_fn refinement or source-candidate adoption, release pins and the
coherent final dependency replay remain open. S4 is not declared fully
closed and the implementation-linked 100-bit target is not established.


## Same callback reaches the selected packed word, including repeated indices

`s4-format-payload-alignment-v1-20261022` proves the source 608-byte opening
prefix/suffix equals the model's kind-0/kind-1 payloads. It establishes byte
framing, not Merkle authentication. Focused exit 0, 16.256s, peak process RSS
3,642,163,200 bytes, swap 0, standard axioms.

`s4-query-returned-model-transport-v1-20261022` retains the same callback
witness and gives conditional transport to a recovered word when its maps
contain that exact opening's bytes. Focused exit 0, 37.795s, peak process RSS
3,941,728,256 bytes, swap 0, standard axioms.

The concrete consumer in `s4-selected-packed-return-v1-20261022`,
`AspisR1.S4SelectedPackedReturnV1.returned_values_match_selected_packed_word`,
instantiates that byte correspondence with the existing global first-occurrence
packed maps. It derives the actual reached position bound from the successful
source query-array read, retains the original source index/cast/opening/dots
success, and proves the actual returned Full values equal the model's four
first-fold inputs at that position. Existing `packed_agrees` and explicit
per-position recovered-map authentication handle repeated indices across
batches; no query uniqueness premise is added. Focused exit 0, 4.557s, peak
process RSS 4,071,997,440 bytes, swap 0, standard axioms. A preceding limited
index-branch-normalization failure is retained. All three packet checkers
passed primary review.

The actual authentication predicates and same parsed-wire binding are still
inputs. In particular, this join does not identify source Prepared.queries
with the transcript-derived model query function. The ongoing sampler review
corrected an interface description: the literal row31 challenge carries a
List Nat of query values, not U32LE-encoded bytes. The missing source/model
link is equality of sampler outcomes under the same absorbed row/payload
and eight oracle block/advance pairs, not a byte codec theorem.

The one-file fast_dots candidate already has retained extraction, optimized
build and fixture evidence. It leaves the frozen weights::powers from_fn
seam intact and still exceeds B1. The existing generated indexed-powers
candidate is now being bound to the full tx2 cut; frozen-source adoption or
Std correspondence remains an explicit unresolved release boundary. No
performance exception or source adoption is inferred here.


## Both candidate caller cuts reach the selected packed-word model

`s4-selected-packed-tx-consumers-v1-20261022` composes the actual ten-query
stage1 and twelve-query settlement consumers with SelectedPackedReturnEvidence.
The exact original caller/callback successes remain, and the same parsed-wire
and per-position recovered-map predicates instantiate the model inputs.
Repeated indices need no uniqueness assumption. Two named public theorems
passed with standard axioms: exit 0, 8.132s, peak RSS 4,075,012,096 bytes,
swap 0. This is conditional source-cut composition; actual Merkle recovery,
source/model sampler equality and source adoption remain open.

## Generated early-powers body removes the S4 candidate P6 powers premise

`s4-early-powers-generated-full-tx2-fields-d18-v1-20261022` binds the actual
retained emitted early_powers::<29> body to ClaimPowers by full Result
equality, then installs that body in the complete candidate tx2 source cut.
The ReaderE composition derives gamma canonicality from the same actual
resume and derives all twelve callbacks' returned local batch values from
the same generated powers result. No independently successful
sourceP6WeightsPowers or caller-supplied gamma canonicality is required.
The candidate patch, generated body/source checker, exact owner pins and
standard-axiom reports are retained. Focused runs: binding 24.576s, full
fields 8.719s, ReaderE/returned values 5.426s; peak process RSS below 4.08 GB.
Swap fields that were not captured are explicitly null, not zero. This is
not final release evidence. Frozen Std/from_fn equivalence and source
adoption are not inferred.

## Sampler retained run, materialized array views, and digest boundary

`s4-row31-literal-run-witness-v1-20261022` strengthens the retained literal
sampler validity result: it now retains the exact list-valued run equality
as well as the decoded Fin22 query function (exit 0, 3.91s, RSS
3,067,379,712 bytes, swap 0, standard axioms).
`s4-row31-source-pairs-join-v1-20261022` proves the corresponding list output
of the ordered eight-pair source schedule under the original prior-state,
absorb, actual read-success and digest-interpretation contracts (exit 0,
5.712s, RSS 3,426,369,536 bytes, swap 0, standard axioms).

`s4-query-array-views-v1-20261022` derives the exact decoded block/advance
list views of the eight actual materialized pair arrays from the existing
schedule witnesses (exit 0, 10.962s, RSS 3,278,569,472 bytes, swap 0,
standard axioms). No independently asserted array-output equality is added.
The parent source-call theorem retains the head state and stateChain needed
for the remaining source-function/array join.

`s4-source-byte-oracle-v1-20261022` gives a byte-addressed presentation of
the existing canonical source oracle and proves its successful canonical
Input calls are interpreted correctly (exit 0, 4.627s, RSS 3,269,935,104
bytes, swap 0, standard axioms). It does not close the actual four-slice
opening absorb: the canonical Input grammar has three slices, and arbitrary
Digest32 dictionaries may distinguish groupings despite equal flat bytes.
The selected SolanaDigest delegates to hashv. The historical J1.R16 runtime
contract/P3 specifies hashing concatenated slices; the current-pin
reacceptance document is a draft and release cluster observation remains
pending. A concrete wrapper/model specialization under that existing runtime
specification is being proved, without claiming a new assumption accepted
or a proof of syscall internals. The canonical third slice for the opening
call is lengthBytes++payload; it must not be confused with a semantic
ValidatedRecord.framed that can include its record tag.

All packet checkers above passed primary review. Prior setup/proof failures
are retained or summarized as diagnostics. These are focused standard-axiom
results, not the coherent final closure. Frozen-source S4 and the complete
implementation-linked 100-bit target remain unestablished.


## Early-powers selected packed outputs and conditional hash regrouping

Primary review checked both new packets' source statements, pin manifests and
retained receipts; both packet checkers pass without repeating compilation.
`s4-early-powers-selected-packed-d18-v1-20261022` composes the actual emitted
early-powers candidate and ReaderE resume with the selected packed-word
bridge for all twelve successful tx2 callbacks. It removes the independently
supplied P6 powers-success and gamma-canonicality premises of the older
consumer. Actual query/model-index correspondence, recovered commitment
authentication, the remaining source-cut operation instances, and candidate
adoption are still required. Its focused run was exit 0, 20.576s, peak RSS
4,066,551,952 bytes, swap 0, with only standard axioms.

`s4-solanadigest-p3-regroup-v1-20261022` proves that the four-slice actual
opening framing and three-slice canonical absorb framing hash identically
in the explicitly defined concatenation-hash model under documented runtime
premise P3. The canonical third slice is length bytes followed by payload.
It does not assert that an arbitrary Digest32 instance has this property,
prove SHA256/syscall semantics, or establish current-release premise
reacceptance. The production wrapper extraction remains a separate task.
Its focused run was exit 0, 20.895s, peak RSS 3,423,780,864 bytes, swap 0,
with standard axioms.

The candidate recommendation now distinguishes the historical gated
b2727-plus-three-blobs overlay from the old experimental branch's ancestry.
No production source, B1 criterion or security contract was changed.
S4 and the implementation-linked 100-bit target remain open.


## P3 interpretation now supplies the functional digest law

`s4-p3-source-interpretation-v1-20261022` proves
`p3_success_interpreted`: every successful call of the explicitly defined
concatenation-hash P3 dictionary is interpreted by
`hashBytes sha256 bs = decodeState (sha256 bs)`, for every input slice
grouping. Thus the generic functional `hdigest` premise used by the row-31
join can be discharged in that model. The same module proves the canonical
source byte oracle agrees with that functional hash on represented inputs,
and interprets the actual four-slice opening through its canonical
length-plus-payload absorb witness. Its default branch is not generalized
into a full random oracle.

The focused target compiled once after correcting a missing retained R4
object-root profile: exit 0, 18.331s, peak process RSS 3,426,369,536 bytes,
swap 0, three reports containing only standard axioms. The initial import
profile failure is retained; no unchanged dependencies were rebuilt. The
packet checker passed. Actual production wrapper refinement, runtime P3
reacceptance and the probabilistic shared-oracle experiment remain open.


## Same source pair list now feeds both sampler views

`s4-query31-materialized-conditional-join-v1-20261022` was reviewed and its
checker passed. `sourcePair_functions_of_chain` derives the exact eight
squeeze/advance success premises from the same successful source execution's
DigestPair list and adjacent state invariant. The composed
`actual_query_row31_materialized_join` retains that execution's decoded
array, materialized blocks/advances and selected state, and the literal
sampler's successful list run and decoded Fin22 function. It derives the
source-array model views rather than assuming them. The focused helper and
consumer runs exited 0, with standard axioms and zero process swaps; complete
receipts are retained in the packet.

The actual B.decode returned array is not yet equated with the literal
query function. Work is split at that precise gap: byte-level query_words
versus State-level words18, then scanner-chain and final-output composition.
The prior-prefix state relation remains required. The generic digest law can
now be instantiated for the proved P3 model, but its production wrapper and
shared-oracle probability law are separate obligations.


## Ordered decoder interface ready for the concrete scanner join

`s4-query-array-order-v1-20261022` reuses
`LiteralQueryRead.decode_success` to prove that an actual Array U32 22
whose value list equals the successfully decoded literal query list agrees
at every Fin22 coordinate with the decoded query function. The theorem
does not supply the list equality: that is the ongoing concrete scanner
refinement obligation. It provides the final ordered coordinate transport
needed for Prepared.queries rather than treating query sets as ordered
arrays. Exit 0, 26.272s, peak RSS 3,452,387,328 bytes, swap 0, standard
axioms. A failed broad simp attempt expanded ofFn; the replacement uses
the symbolic getElem?_ofFn lemma. Diagnostics and the focused checker are
retained. No dependencies or unchanged full regression were rebuilt.


## Candidate entry now derives both successful execution and exact batches

`s4-candidate-total-local-values-v1-20261022` composes the retained
source-body-checked concrete V10 entry endpoint, strict opening decode and
the width29 kernel theorem. `candidate_entry_total_exact_batches` derives
the complete entry result, all four returned canonical values and their
exact four width29 batch meanings for the same decoded source opening.
No successful entry/helper/callback call or independently chosen typed
opening is assumed. Canonical gamma, the same ClaimPowers output, incoming
coefficient-array identity and strict scanner/frame inputs remain explicit.
This strengthens the earlier accepted-call-only value consumer; it is still
a candidate helper theorem rather than frozen-source or global soundness.
Focused run: exit 0, 29.334s, peak RSS 3,999,563,776 bytes, swap 0, standard
axioms. Initial binder syntax failure retained; no unchanged dependencies
were rebuilt. Packet checker passed.

The isolated three-file candidate is published for concrete review in
draft PR https://github.com/DJBarker87/aspisZK/pull/10. It is unadopted and
unmerged. The draft explicitly retains all six B1 CU comparison failures,
source/refinement obligations and the implementation-linked target. It does
not propose merging the historical experimental branch wholesale.


## Installed candidate dots slot no longer assumes dots-call success

`s4-queryops-total-local-values-v1-20261022` installs the total exact
candidate entry into the existing concrete QueryOps builder and derives
the same returned Full array's exact local batch values through the retained
carrier decoder theorem. Compared with
`concrete_candidate_dots_success_has_endpoint_fields`, the new
`candidate_queryops_dots_total_exact_batches` has no successful dots-call
`hcall` premise and no preselected returned array. It derives them from the
same strict frame/scanner and canonical incoming powers contracts. No
rejection path is discarded from a claimed all-input result: the theorem is
explicitly scoped to those checked inputs.

Focused run: exit 0, 25.195s, peak RSS 4,050,337,792 bytes, swap 0, standard
axioms. Packet checker passed; no unchanged dependency was rebuilt. This is
forward totality for the installed candidate dots slot, not complete query
or caller totality. Candidate adoption, frozen-source lowering and global
authentication/sampler/runtime/security composition remain open.


## Actual per-block source decoder now matches the sampler words

Primary review of `query31-byte-sampler-bridge-v1-20261022` checked the
source statement and packet checker.
`AspisR1QueryWordsSamplerBridgeV1.query_words_success_sampler_words18`
proves a successful actual extracted query_words call returns the exact
ordered eight words `SamplerWords.words 18 (decodeState block)` for that
same byte block. It reuses the source byte-mask theorem and retained
SamplerWordBridge.source_word / array roundtrip, so no independent byte
interpretation or model-word equality is assumed. The record-by-record
little-endian window and 18-bit mask correspondences are derived.

Focused run: exit 0, 6.921s, peak aggregate RSS 3,268,329,472 bytes, swap 0,
standard axioms; exact source/object pins and zero-missing selected closure
retained. This closes the per-block decoder-value gap. The same DriverTrace
first-stop/scanOut and finish-output composition is still in progress;
complete query output, prior-prefix, production hash-wrapper and shared
oracle law are not inferred from this local result.


## Generated powers-to-dots forward pipeline and finish projection

`s4-earlypowers-dots-total-v1-20261022` reuses the actual emitted
early-powers binding and its all-N mathematical totality theorem at the
actual N=29 monomorphization. From canonical source gamma and the strict
scanner/frame contracts it derives the successful generated powers result,
its coefficient identity, successful installed dots result and exact four
local batch values. No independently successful powers/dots call, chosen
power array or coefficient-map equality is a premise. This strengthens the
previous slot theorem by deriving those intermediate contracts. It remains
a candidate helper pipeline: no caller reachability, authentication,
transcript gamma/query relation or probabilistic security is inferred.
Focused exit 0, 8.496s, peak process RSS 4,037,410,816 bytes, swap 0, standard
axioms. An initial missing retained early-prefix import closure failure is
recorded; the successful retry appended the parent's pinned profile without
rebuilding unchanged modules. Packet checker passed.

`query31-finish-accepted-values-v1-20261022` was separately reviewed and
its checker passed. `finish_success_accepted_values` derives the exact
returned array's natural-value list from the same terminal source state's
Q22 accepted list. Successful finish supplies accepted_len=22; the source
array length makes its accepted prefix the full returned array. No valid
state or independent finish-output equality is assumed. Focused exit 0,
11.886s, peak aggregate RSS 2,229,354,496 bytes, swap 0, standard axioms.
The source trace/first-stop construction is still open and remains distinct
from this local finish projection.


## Extracted production hash wrapper bound conditionally under P3

`s4-solanadigest-wrapper-p3-binding-v1-20261022` was reviewed, including
the exact functionalized emitted body and packet checker. The focused
source cut retains the production SolanaDigest fragment and exact trait,
Hash representation and Hash::to_bytes bodies. Charon and Aeneas succeeded
on the NUC in capped swap-free scopes. The single external hashv operation
is made an explicit parameter in the checked body adapter; its P3
instantiation is the already documented concatenation hash model. Generated
FunsExternal_Template is retained only as diagnostic source and is never
imported by the accepted proof. No external hash/SHA axiom is introduced.

`p3_digest_method_eq_model`, `p3_public_record_eq_model` and
`p3_current_record_eq_model` connect that emitted method interpretation and
the two nominal dictionary records, with the Copy/Clone interpretation
explicit. Focused wrapper run: exit 0, 8.862s, peak process RSS
3,467,362,304 bytes, swap 0, named reports standard axioms only. Exact
source, dependency/tool, emitted-body and output pins are in the packet.
This closes the checked wrapper-method bridge under P3; it does not prove
SHA256/syscall internals, actual whole caller instantiation, current-release
P3 reacceptance or a random-oracle probability law. The next consumer
specializes the actual row31 sampler to this dictionary and derives its
functional digest law instead of assuming it generically.

The proposed isolated inline(always) optimization was found already tested
in retained work (`/tmp/s4-combined-inline-v2-20261021`); outputs and strict
stack checks passed but all six B1 comparisons failed. It was not rerun.
Candidate source adoption and B1 policy remain unresolved.


## Exact source-pair views and corrected scanner recursion interface

`s4-pair-function-views-v1-20261022` proves
`materialized_pair_function_views` from the existing same-pair
materializedOutputs witness alone. Both decoded source arrays equal the
range-8 list views of sourcePairBlocks and sourcePairStates(k+1). It does
not assume stateChain, hash interpretation, pair length or independent
array alignment. It supplies the direct list views needed for the scanner
output join, avoiding independently selected existential source witnesses.
Focused exit 0, 22.288s, peak process RSS 3,220,766,720 bytes, swap 0,
standard axioms. Packet source and checker were reviewed.

Primary review found that the earlier experimental Run.stopped interface
forced the fallback input state to equal the current advance state. That
restriction does not follow from the implementation. The corrected
`s4-scanout-run-core-v1-20261022` quantifies the fallback independently and
proves scanOut_of_run with the actual selected output state; no equality
between distinct oracle outputs is assumed. Exit 0, 8.376s, peak process
RSS 3,423,502,336 bytes, swap 0, axioms propext and Quot.sound.
`s4-trace-literal-output-join-v1-20261022` separately composes an exact
scanOut array-value result and same-pair literal result into array/list
output equality. Its traceResult premise is the concrete array's scanOut
result, not the desired equality with literal xs. Exit 0, 4.494s, standard
axioms and zero swaps. Both packet checkers passed. The actual production
DriverTrace-to-Run construction is still being proved, not assumed closed
by these generic composition helpers.

## Row31 cut specialized to the source wrapper's P3 interpretation

`s4-query31-p3-materialized-join-v1-20261022` fixes the source-shaped
QueriesModel cut's dictionary to p3PublicDigest32 sha256 and functional
oracle to hashBytes sha256. It derives the former generic hdigest contract
using the wrapper equality and p3_success_interpreted, preserving the same
source witnesses, prior-prefix hstate and successful literal run. Exit 0,
4.525s, peak process RSS 3,464,429,568 bytes, swap 0, standard axioms.
Source statement and checker reviewed. No SHA/syscall or ROM law is added.

The unchanged production queries_from_pairs is still distinct from its
retained unrolled source-shaped candidate. Prior full extraction deliberately
made the production helper opaque. A new focused extraction of its unchanged
outer loop is underway, retaining scan/finish callee boundaries. Neither
the P3 specialization nor the forthcoming model scanner composition may
be described as full production sampler refinement until that source
boundary is discharged. Frozen-source S4 and global soundness remain open.


## Concrete first-stop trace now yields exact scanOut output and state

Primary review checked the source and checker of
`query31-driver-trace-scanout-v1-20261022`.
`successful_driver_trace_scanOut` consumes the same full block/advance
arrays and actual first-stop DriverTrace, valid initial scan state and zero
initial draws. It proves the entire scanOut pair equals the returned query
array's value list and the decoded selected advance. Its model starts at
q22StateOf that actual initial state; the source default lemma supplies q0
for the default specialization. All eight stop cases are covered, including
the final lastStop=false shape by continuing into the zero-length finish.
Earlier advances are derived from the typed array, never assumed as source
reads. False scans derive draws=8*i, keeping each visited guard below 64.
Focused exit 0, 16.066s, peak process RSS 3,509,338,112 bytes, swap 0,
standard axioms. The packet honestly records that earlier temporary failed
attempts were overwritten; only the final successful attempt has complete
source/receipt/log evidence. No missing diagnostic is fabricated.

`s4-row31-source-trace-consumer-v1-20261022` internally discharges the
pair-array views from the same materializedOutputs witness and combines
that source scanner result with the literal same-pair result. It derives
array-value-list equality with literal xs; no desired output equality is
assumed. Its exact traceResult input can now be supplied by the theorem
above. Focused exit 0, 20.636s, peak aggregate RSS 3,426,779,136 bytes,
swap 0, standard axioms. Source and packet checker reviewed. The next
entry-level consumer eliminates independently supplied pair/array/trace
witnesses using one full successful chosen-model query schedule.

`s4-query-zero-counter-start-v1-20261022` proves zero accepted/draw counters
project any typed backing array to q0 and yield validState. No backing-array
zero-content property is needed for that projection. Actual source default
counter provenance remains to be supplied by the constructor extraction;
the theorem does not assert full source-state equality or prove Std
DefaultArray. Focused exit 0, 15.322s, peak process RSS 2,251,194,368 bytes,
swap 0, standard axioms. Metadata normalizes one direct module identifier
from path spelling to Lean spelling without changing compiler execution;
original metadata and explanation retained. Packet checker reviewed.

The unrolled source-shaped DriverTrace and the unchanged production
queries_from_pairs loop are still distinct. The production-loop extraction
and refinement remain required; none of these results is a source adoption
or an implementation-linked security theorem.

## Chosen-model query acceptance, with no literal-success premise

Primary review inspected the complete statement and proof of
`s4-chosen-model-row31-acceptance-v1-20261022` and its actual named axiom
report. `successful_queries_row31_literal_acceptance` starts from one
successful `QueriesModel.queries` execution under concrete scanner boundaries
and the explicit P3 digest interpretation. It derives literal byte-sampler
success, the same ordered 22 query values, and exactly
`decodeState after.state` as continuation state. No successful literal run,
independently aligned pair list or desired output equality is a premise.
The proof reuses the same schedule witness, concrete first-stop trace and
full scanOut pair, source prefix transport, and literal decoder theorem.
Framed-payload fit and prior-prefix state equality remain premises. This
does not discharge actual production-loop refinement or SHA/syscall/ROM laws.
Focused exit 0, 38.049s, peak aggregate RSS 3,432,693,760 bytes, swap 0;
the named report contains only propext, Classical.choice and Quot.sound.
The packet checker passed without rerunning unchanged Lean.

The earlier `s4-chosen-model-row31-query-v1-20261022` remains as the
conditional coordinate transport: it assumes successful literal sampling.
Its README and checker explicitly preserve that narrower scope.
`s4-literal-row31-pair-state-v1-20261022` additionally transports a supplied
successful literal run backwards to the entire source pairsRun result,
including continuation state. Its focused run exited 0 in 19.404s, peak
process RSS 3,443,949,568 bytes, swap 0, standard axioms. Failed attempts
are retained and rejected. All three source-only packet checks passed.

The next work is restricted to S4's frozen array/from_fn source boundary
and its stage-1/stage-2 caller instances. The sampler results are preserved;
they are not a reason to expand the S4 closure task into further adjacent
sampler work. Candidate adoption remains unapproved and the strict B1 gate
remains failed. Frozen S4 and the implementation-linked 100-bit target
remain open.
