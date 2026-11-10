# NPR_ R22 final counts (CheckedVsWrapping), 2026-11-10, local continuation of NPH_

Job NPR_, branch codex/cx-r22l-20261110, run locally on the Mac (no build host). This file is a copy of NPH_R22_FINAL_COUNTS.md with NPR_'s changes; NPH_'s file is unchanged. Frozen target 4bb3b3f (deployed ELFs f8c0ec72…, 63ad3e9c…, built with overflow checks OFF). Machine record: NPR_R22_CONE.json, generated from NPH_R22_CONE.json by NPR_cone_update.py and recounted by NPH_recount.py. **Target not yet established.**

## 1. Counts

| Judgment | Definitions | Start of this run (NPH_) | Change |
|---|---:|---:|---:|
| TOTAL (a) | 72 | 72 | 0 |
| DIRECT (c) | 52 | 52 | 0 |
| precondition proved from the callers (b) | 72 | 71 | +1 |
| domain lemma proved, caller join open | 0 | 1 | -1 |
| open | 1 | 1 | 0 |
| NOT_EXECUTED (excluded, ruling 1) | 28 | 28 | 0 |
| **executed (the obligation)** | **197** | 197 | 0 |
| all checked or mixed | 225 | 225 | 0 |

Rows. The executed checked or mixed definitions touch **393** CLOSED rows. **27** of them still depend on an open definition (44 at the start of this run). 366 are served only by TOTAL, DIRECT or (b) definitions. The 17 rows removed are exactly those for which weights.field was the only blocker; the 27 that remain are r24_canonical_mul's rows, and it is the only blocker for each of them.

Validation. Every compile was local, one Lean process at a time: toolchain leanprover/lean4 v4.32.0, `lean -M7000 -DElab.async=false`, a 180 s alarm, LEAN_PATH = the replayed L187 closure (objs, base) + overlay-NPH (the 52 NPH_ export objects fetched read-only from the host, hashes in NPR_OVERLAY_NPH.sha256) + overlay-NPR. There were 21 compiles: 3 probes, 17 module attempts and 1 axioms audit. 13 exited 1 and each was changed before the next. Every row is in NPR_COMPILE.tsv, with logs in NPR_logs/. The longest wall time was 60.06 s and peak RSS 5,574,295,552 bytes (5.19 GiB). This Mac has no cgroup, so the only memory cap was Lean's own -M7000. Host swap in use (vm.swapusage) was 6.5 GB before the first compile and stayed between 7.7 and 7.8 GB during the run. The swap is recorded, not zero. The final audit (NPR_Audit, NPR_C021, exit 0) prints 39 `#print axioms` lines. Each is within [propext, Classical.choice, Quot.sound]; question_err depends on no axioms. There is no sorry, no native_decide and no raised -M. There was no host job, extraction, manifest replay, push or deletion. Accepted modules and their final compiles: NPR_R22WeightsWidth (C004), NPR_R22DotSite (C008), NPR_R22ClaimSite (C010), NPR_Screens (C016), NPR_R22LiteralSites (C020). NPR_OVERLAY_NPR.sha256 records their objects. These are focused compiles against cached closure objects, not a coherent rebuild of the release closure.

## 2. What moved in this run

**weights.field: domain lemma proved → (b).** Its three index operations i·32, i+1 and (i+1)·32 are ok for i < 64 (NPH_R22FieldSites.domain_ok). NPR_ proves in Lean that every executed call supplies an index below 64. The statements are congruences: replacing a slot by a copy that fails outside the domain leaves the deployed function unchanged on every input. So an out-of-domain call never executes, and no acceptance of a later call is used.

1. **Finish dot, weights length (producer 1).**
   - `NPR_R22WeightsWidth.query_domain`: from the resume Domain start, NJJ_Common.query (op6 of the deployed tx2, NNU_Query.source) returns a state reached by successful query_values steps on Dcon. That is an NPH_R22JoinCW2.Reach state, so it has NFS_QueryInvariant.Domain: weights width 64 and pending raw length 64 (`run_reach`, fuel induction through NFG_QueryLoopDefs.run and NFS_QueryLoopRoot.finite).
   - `width_at_finish`: the prefix successes before the finish call give a flushed slice of length 64. They are the resume (NPH_R22JoinCW2.entered_domain), the guard a.next = SPLIT = 10, powers (NNU_Query.powersDomain), pending (NNH_Run5bQueryDomain.initial), query and flush (Port3_FlushInstall.accepted_contents: length preserved when old ≤ raw).
   - `run_finish_congr`: for every input and observer, NJJ_Common.run calls its finish only on accumulators whose weights have length 64.
   - `deployed_common_guarded` (no premise): LIBB_Tx2EnvCode.common env pub proof ck equals the same run with the finish guarded on width 64.
   - `NPR_R22DotSite.finish_op4_congr`: the native finish calls op4 only on Vec.deref a.weights. `deployed_finish_guarded` and `deployed_common_dot` (no premise) then show that the deployed tx2 common runs its finish dot only on slices of length 64.
   - `installed_op4_source` (rfl): that op4 is SAG_DotAdapter.sourceDot SAG_DotClosed.seed.
   - `kernel_guarded`, `dot_guarded`, `dot_loop_field_congr`: on a slice of length ≤ 64, the dot kernel (finish_query_dot on mapSlice toFinishQ) calls its field slot only at j < 64. That slot is finishField (`NPR_Screens.dot_record_field`, rfl).
2. **Claim dot, iterator bound (producer 2).** `NPR_R22ClaimSite.claim_guarded` covers borrowed_abi.owned_claim_loops for any ClaimDotOps: the claim calls its field slot only at l < 29.
   - The proof is the generic `loop_congr_inv` (measure induction through loop.eq_def), with `inner_body_cont`/`inner_body_congr` (NHI_RangeProgress.some_next on the inner range {0, 29}), `inner_congr`, `outer_congr` and `claim_loops_congr`.
   - The deployed claim body is owned_claim_loops on concreteOps QRaw (NPH_R22JoinCW5.claim_body, rfl, reached through originalNew_guarded).
   - Its field slot is ClaimParser.field, which calls finishField (`NPR_Screens.claim_record_field`, `claimParser_body`, rfl).
   - `claim_site_reached` composes NPH's claim_site.
3. **Literal sites.**
   - `NPR_R22LiteralSites.round_guarded`: Port4D_Round.round calls its field slot only at 0 and 4.
   - `poly_guarded`: the deployed Horner polynomial (FIn_Extract.FIn_reference.polynomial on FIn_ExtractInstall.arithmetic) calls its field slot only at 6, 5, …, 0.
   - `deployed_round_slots` and `arithmetic_field` (rfl): op5 of NIG_Slots.installed r is that round, and both field slots are FIn_Primitives.field, which calls finishField (`primitives_field_body`).
4. **The callee.** finishField calls weights.field at its own index argument (`NPR_Screens.finishField_body`, rfl).

What the move still relies on, as every other (b) move does: the reading that finishField is weights.field's only referrer (NPH_REFS6.json, section 4), and the P6/P7 reading of the operational tree as the compiled code. One claim loop is not covered: CurrentClaimDotModel.prepared_claim_dot, which NPH_R22FieldSites named alongside the borrowed loop. NPH_R22JoinCW5 shows the deployed prepare runs the borrowed claim. If any executing path to prepared_claim_dot is found, the same loop_congr_inv argument applies (its iterator is also {0, 29}), but it has not been proved here.

The guarded definitions (widthGuard, op4G, runRowG, expandValuesG) are statement devices in NPR_ modules. No ops interface, merged module, closed-row statement, field premise, trust row or contract is changed. NPR_R22_CONE.json records the previous judgment under `npr_judgment_before_wf`.

## 3. Definitions still open (1)

| Rows | Only blocker | Definition | Pattern class | What closes it |
|---:|---:|---|---|---|
| 27 | 27 | `AspisR72Sampler.field.r24_canonical_mul` | NO_FROZEN_COUNTERPART | provenance first: a source-refinement obligation with no frozen source, not an R22 arithmetic gap. Once the body is pinned, its checked operations have the Q.raw shape (u64 products of widened u32 limbs, 2u, 2v, 3P), and NPH_R22QRawTotal should apply. Not proved. |

## 4. Textual-screen reliances: replaced, partly replaced, or remaining

Each NPH_ section 4 reliance is listed. "Replaced" means the relied-on fact is now a Lean theorem (module NPR_Screens unless noted). "Remaining" items are negative claims such as "no other caller exists" or a fact outside Lean. Each remaining item is named here for owner review: a release claim must either accept it by name or replace it.

| NPH_ reliance | Status | Lean statement / what remains |
|---|---|---|
| op9 → prepare → tx1 → op10 → first_decoded → stage1_owned chain (SM, FIq) | **Remaining (R-1)** | Negative: "op9 is read once, prepare is called once, op10 is read once, …". The positive part is already in Lean: NPH_R22JoinSM7/JoinFIq.stage1_guardedT, with no premise. NPR_ adds `current_is_installed` (rfl): the deployed adapter record NNH_Run5bCurrentShape.current m env err r is DrvC_Installation.currentInstalled (NNH_CorrectConfiguration.configuration m env err r). |
| Call-pattern reading of Port3_NativeQueryBody/GeometryBody: executed dictionaries Dcon/Dsel | **Replaced (dictionaries)** | `tx2_query_base` (rfl) and `tx2_query_Dcon`: from a Domain start, NJJ_Common.query runs query_values on Dcon at every step. `libc_model_base` (rfl) and `libc_model_Dsel`: LIBC_QueryLoop.model runs query_values on Dsel at every step. With NNU_Query.source (stage op6 = NJJ_Common.query), the tx2 dictionary is Lean. |
| same: which QA callbacks the bodies invoke; the geometry stage path | **Remaining (R-2)** | Completeness of the callback enumeration inside query_values and the geometry body (negative: no other slot call). Not addressed. |
| NPH_SITES.json site checklist (CW, SM, QA, SC, R72, FIq) | **Remaining (R-3)** | Completeness of the site list (negative). |
| NPH_FIQ_REFS, NPH_SUM3_REFS and the SC referrers, NPH_R6X_REFERRERS, NPH_REFS4_A, NPH_REFS5, NPH_REFS6, NPH_REFS7 (backward referrer screens; NOT_EXECUTED exclusions; "X only from Y") | **Remaining (R-4)** | Negative referrer claims. For weights.field, NPR_ makes every positive path Lean (the finish dot, claim and literal sites above, and finishField_body). That finishField is the only referrer still rests on NPH_REFS6.json. Suggested replacement: a Lean-environment referrer scan over the elaborated terms of the replayed closure, which sees through notation and instances. It is not built here because of the 8 GiB local cap. |
| parse_record_at Err(Length)/abort | **Partly replaced (R-5)** | `question_err` (rfl, no axioms): a `?` on an Err result returns that Err without running the continuation. Remaining: that each of the parse_record_at calls in r1_wire.Prefix.parse is followed by `?`. This is a structural reading of the extracted body (AspisR1PrefixAggregateParser/Funs.lean, Prefix.parse); a stepping proof was not attempted within the compile budget. |
| GammaHelpers record at the executed gamma_sample | **Replaced** | `deployed_gamma`: (installedBoundaries S e).gamma = candidateGammaPublic, through installed_as_candidate_samplers. `candidateGammaPublic_body` (rfl): it runs gamma_sample on candidateGammaHelpers. NPH_R22Gamma.helpers_low gives that record's low = low_base_p_digits. installedBoundaries S e is the deployed sampling of NPH_R22JoinCW5.originalNew_guarded. |
| Checked-operation enumeration of each DIRECT/TOTAL-by-pattern body (NPH_LOOPS_SCREEN, census screen, NPH_hostops/hostbody) | **Remaining (R-6)** | Completeness of each body's checked-operation list (negative). It could be replaced by an elaboration-time scan of each body's term for checked-arithmetic constants; not built here. |
| Dots inner body: range index, try_from, unwraps and decode abort in both profiles | **Remaining (R-7)** | Not a Lean fact. This is a property of the compiled profile: bounds checks and panics are profile-independent in Rust, and overflow checks are the only profile difference. It belongs with the P6/P7 compiler trust lines (NOX_REALIZATION.md). |
| Call-site bindings of the two expandValues sites | **Replaced** | Compact site: `runRowG_eq` and `compact_body_guarded` show that the compact expand loop body (= JFw_Row.runRow by the existing JFw_Row.factor) calls expandValues only on a payload of length ≤ 1856 at every row with a row_shape (NPH_R22Values.compact_site). Prepare site: `candidate_op11_congr` (candidate.prepare calls op11 only on proof[OFF_Y1, OFF_INACTIVE)) and `installed_op11_guarded`, which says that at every installed configuration op11 runs only on slices of length ≤ 1856 (NPH_R22ValuesSite.installed_y1_site). |
| NDO_JFw_Row.runRow copy of the compact row body | **Replaced** | JFw_Row.factor (existing, NDO_JFw_Row): compact.expand_semantic_loop.body nativeValues … = runRow, composed in `compact_body_guarded`. |
| Executed prepare record (closure reading) | **Replaced** | `current_is_installed` (rfl), as above. The per-configuration statements NPH_R22JoinCW6.installed_prepare_guarded, NPH_R22Values.installed_ls and `installed_op11_guarded` apply to the deployed record. |

Separate from the screens, and unchanged: the reading of the operational tree as the compiled code is the P6/P7 interpretation (Aeneas translation fidelity and the compiler trust lines of NOX_REALIZATION.md); Lean does not load the ELF. The NOT_EXECUTED exclusions apply lead ruling 1 by principle (R-4).

Owner-named review items: R-1 to R-7 above.

## 5. Proposed wording for the claim document (section 4.3, CheckedVsWrapping row)

> **CheckedVsWrapping (R22, OPEN).** The gate's emitted bodies for the reached definitions are checked translations, in which an overflow is an error result. The deployed ELFs (f8c0ec72…, 63ad3e9c…, built from 4bb3b3f) wrap. The theorem transfers to the deployed binary when every executed checked or mixed definition meets one of three conditions: its checked body is total on every input (TOTAL); it is total on a domain that its reached callers are proved to supply ((b)); or wrapping acceptance is proved to imply checked acceptance directly (DIRECT). R22TotalCheckedComposition then gives safety of every executed checked operation and equality of the wrapping and checked results, under the P6/P7 interpretation of the operational tree as the compiled code.
>
> Status at 4bb3b3f (NPH_ and NPR_, evidence/r22-final-20261110/NPR_FINAL_COUNTS.md): there are 225 checked or mixed definitions. 28 of them are proof-only references, excluded under lead ruling 1 on textual referrer screens. Of the 197 executed, 72 are TOTAL, 52 DIRECT and 72 (b); 1 is open. 27 of the 393 CLOSED rows these definitions serve depend on that open definition. No reachable input on which the wrapping binary accepts and the checked model rejects is known. The Merkle traversal subtraction, the one site where such an input could have arisen, is proved safe on every reached state (NPH_R22Binary). The weights-field index is proved below 64 at every executed call of the deployed tx2 finish, the claim dot and the literal sites (NPR_R22WeightsWidth, NPR_R22DotSite, NPR_R22ClaimSite, NPR_R22LiteralSites).
>
> Residual: r24_canonical_mul alone. It has no frozen counterpart, so this is a source-refinement obligation and not an arithmetic gap of this row.
>
> Removal condition: every executed definition is in (a), (b) or (c) on the final replayed closure, and each remaining textual reliance (NPR_FINAL_COUNTS.md section 4, R-1 to R-7) is either replaced by a Lean statement or accepted by the owner as a named review item. Otherwise the owner records R22 as a retained trust row, named in the claim's first sentence.

The 2021 figures (35 TOTAL / 63 ACCEPTED-ONLY / 48 OTHER of 146 statements) concern a different object and remain superseded for this row.

## 6. Appendix: row IDs of the open definition

- `AspisR72Sampler.field.r24_canonical_mul` (27): TX1:087, TX1:094, TX1:136, TX1:137, TX1:142, TX1:156, TX1:168, TX1:169, TX1:170, TX1:186, TX1:328, TX1:330, TX1:333, TX1:344, TX1:345, TX1:NGB002, TX1:NGB004, TX1:NGB006, TX2:151, TX2:197, TX2:198, TX2:199, TX2:200, TX2:213, TX2:220, TX2:221, TX2:225

Next concrete deliverables: (1) r24_canonical_mul provenance (pin the source body, then apply NPH_R22QRawTotal); (2) a Lean-side referrer and checked-operation scan to replace R-3, R-4 and R-6; (3) a stepping proof of the parse_record_at `?` propagation through r1_wire.Prefix.parse (R-5); (4) the coherent replay of the final dependency closure with these modules, which only a build host can do.

Target not yet established.
