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
