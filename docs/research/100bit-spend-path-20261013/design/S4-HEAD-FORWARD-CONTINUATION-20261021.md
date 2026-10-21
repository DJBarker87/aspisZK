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
