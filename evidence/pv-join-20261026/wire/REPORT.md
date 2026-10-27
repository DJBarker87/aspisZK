# Wire report

**Target not yet established.** This task organises proved facts into the candidate consumer closure. No privacy endpoint premise is discharged and no headline credit is claimed.

Branch: `codex/pv-join-20261026`. Base: `908f14a854`. Both requested git-only callback branch merges succeeded without conflicts. Commit history: `commits.txt`; no push. No shipped-code, wallet/key, Kani, root-checkout or sibling-file edit.

## Result and exact boundary

Recount 3 research/candidate/neither import counts **0/17/10 → 0/26/1**, same 27 CLOSED-ON-CANDIDATE rows. All 26 closing source-law declarations are now proof dependencies of `R1Z.PV_Join_Wire_Caller.refinement_of_data`, defined in `PV_Join_Wire_FinalAuditA.lean`; the final audit requires that caller and reports its declaration graph. Arbitrary-carrier `PV_CB3_Op51Arbitrary.op51_source` is additionally consumed, without changing Recount 3’s OPEN op51 disposition. The graph reports 28 source-law declarations in total: the required 27 plus the underlying op51 source theorem.

The nine formerly neither operation laws are V197/71, V206/84, V209/100, V210/101, V212/107, V213/109, V214/110, V218/118, V219/120. V270 is the tenth neither row; it is a scoped Formatter axiom-route diagnostic with no closing operation theorem. `IMPORT-CHAIN.md` records it as **not reachable**, with the reason. Native Formatter adequacy V269 remains open.

Import membership overstated actual use: only 15 of the 26 closing source theorems occurred in the historical caller’s proof graph. The 11 unconsumed closing declarations (including already-imported V242/225 and V246/229) and all exact names are listed in `IMPORT-CHAIN.md`; all 26 are now consumed. `import-chain.json` contains every path edge, source hash, baseline label and checked proof-membership bit for mechanical Recount 4.

The dictionary proof applies one exact consumer equation per operation, at the callback it selects. These equations retain arbitrary raw carriers, callback failures/divergence and complete Result/Option. Ops 84/105/107/109/118 use the newly merged exact source laws. Op225’s source theorem permits arbitrary payload adapters because the projection ignores payloads; total constant adapters in the function normal form add no representation assumption. Op229 uses its existing explicit native carrier conversion.

## Before/after hypotheses

The historical published aggregate statement is unchanged. The new caller uses the source-wired selection on its P6 aggregate baseline, over arbitrary `base` with the existing `native base` carrier for op229. It retains exactly the reservation equation `store.reserve s digest attempt.mask_nonce = ok (accepted, after)` and the complete data equation `data (execute selected ...) = model`, concluding `execute selected ... = withState after model`. No new Prop hypothesis, canonicality, totality, algebra or source/model equation is added. No premise is removed. The selection changes are explicit; this task does **not** prove all new selections equal the historical dictionary.

Native interpretation/effects/world and release association, the actual source/model data equation, RunJoin, E1/E2, L1/L2/L3, client/adoption and release replay remain obligations. Research `PrivacyR1HeadlineDeployedReal.privacy_headline_deployed` imports none of the new consumer work. Auditing that headline alongside the candidate creates no reverse dependency or headline credit.

## Validation and failures

All **60/60** Lean compile attempts used, IDs **39300–39359**, no reuse or barrier refusal; next unused ID 39360, compile budget exhausted. All runs used the restored host launcher, Lean -M7000, MemoryHigh 6G / MemoryMax 8G / MemorySwapMax 0 / TasksMax 64, one scope at a time. No local Lean compile or Kani run. **54 green, 6 failed**. Every failure is retained; no unchanged failed job was rerun.

39326: op246 direct extracted selection differed from the alternate hash-selection form. 39327: an over-broad rewrite had already solved the goal. Replacement 39328 uses explicit equality transport and passes. 39340: implicit polymorphic binders in a let-instance function type shifted lambda arguments; explicit binders and function references pass at 39341. 39345: a source-function name shadowed its imported op229 source; fully qualifying it passes at 39346. 39356: the theorem itself elaborated with standard axioms, but the auxiliary graph command had ill-formed syntax; the command was removed. 39357: the first reserved audit omitted the dictionary import, so that audit is rejected. The corrected audit explicitly imports all modules and merges both statement inventories. No failed elaboration’s generated placeholder is accepted.

Final three attempts were reserved for the combined audit: 39357 failed, **39358 and 39359 passed**. The final sources cover 183 other PV_Join modules plus the audit declaration module and combined wrapper; all 292 inherited/new proof/function names, all 27 required consumed laws, and the research headline are audited. 39358 prints complete statements and 321 standard-axiom reports; 39359 prints 320 standard-axiom reports and the consumer declaration closure. Accepted axiom sets are subsets of `{propext, Classical.choice, Quot.sound}`. This is a focused combined dependency/axiom audit against retained host objects, **not a clean release manifest replay**.

| Final target | ID | Exit | Wall | Peak RSS KiB | Swap | Source revision |
|---|---:|---:|---|---:|---:|---|
| `R1Z/PV_Join_Wire_FinalAuditA` | 39358 | 0 | 0:09.90 | 4376500 | 0 | `46fd1054ff370779c060a250281c4c37ff62aac9` |
| `R1Z/PV_Join_Wire_CombinedAudit` | 39359 | 0 | 0:03.05 | 4343380 | 0 | `46fd1054ff370779c060a250281c4c37ff62aac9` |

Every attempt’s target, exit, wall, peak RSS, swaps, exact revision, source/dependency fingerprints and full `#print axioms` result are in `receipts.json` and the per-ID input/receipt/out/time logs. `final-source-check.json` verifies all 54 final new Lean source modules match successful compiled bytes. Draft generators are retained but disabled; final audit source and manifest are pinned.

Stopped on budget exhaustion after the successful final combined audit. Next deliverable: Recount 4 should consume `import-chain.json`, set the 26 source rows to candidate-reachable, and retain V270’s reason. Subsequent proof work must address the actual model/native/release joins; this wiring supplies no discharge for them.
