# TFM top statement form and allocator association

Target not yet established. This report decides two questions left open by TAS_. It closes no row and adds no trust. It proposes one change to the top statement, which goes to the owner (TFM_OWNER_MEMO.md). Base: `research` at c3340652424. Headline sources were read from `evidence/replay-deployed2-20261027/RPx_Deployed.lean` and the files it imports (`RPv_FJv_Top`, `RPv_FJv_Observations`, `RPu_FJp_Observations`, `RPu_FJp_ARCore`, `RPx_FJv_DBoundCaller` for `FJv_DResult.Outcome`, `lean/FJp_Residual`, `lean/FJp_Mass`, `lean/F3T_*`, `lean/F3Y_AccountMass`). `lean/FJp_ARCore.lean` is byte-identical to the replayed `RPu_FJp_ARCore.lean` once module prefixes are removed.

## 1. Question 1: can the top have the exact headline shape?

### 1.1 Where `accepted2` is consumed

The headline proof is `FJv_Top.deployed` followed by a replacement of conjunct 4 by `FJv_DNativeAccepted.accepted`. `FJv_Top.deployed` calls `FJv_Observations.observations`. That calls `FJp_Observations.observations`, which calls `FJp_ARCore.observations` and adds `S6N_Installation.facts`. Each layer passes `accepted2` down as an argument, but only the branch that builds conjunct 4 uses it. The table lists the term that proves each conjunct in `FJp_ARCore` (or the layer named) and what it consumes.

| # | Conjunct | Proof term | Consumes | Root0-free source at the top |
|---|---|---|---|---|
| 1 | P6 boundary | `P6C_Extension.boundary hashv sha256 H p1 syscall` | retained binders only | none needed |
| 2 | driver = source | `DrvC_SourceEntry.same_program …` | configuration | none needed |
| 3 | sdk = dictionary | `DrvC_Installation.aus1_dictionary …` | configuration | none needed |
| 4 | `FJv_DResult.Outcome … (event)` | `FJv_DNativeAccepted.accepted …` (FJv layer: `FJp_Ret_Rc7Native.accepted`; ARCore: `FIs_Rc7_Native.accepted`) | **accepted1, accepted2, game, extraction** | **none: needs model TX2 acceptance, which needs Root0** |
| 5a | three Claims | `F3X_ModelClaims.claims`, `FJp_Cost.source_cost`, `F3Y_AccountMass.claims` | queries, finish owners, matching law | L154 + configuration |
| 5b | three numeric clauses | `FJp_Residual.numeric` with `F3U_Range.per_attempt`, `F3U_Numeric.runtime_margin` (FJv_Top) | extraction, queries, owners | A0 (extraction at the models) + L154 |
| 6 | copy facts (`saved.val.length = 1768`, …) | `PoolT_Write.accepted_verifier_writes_copy … accepted1` | accepted1 | TX1 alone (A3 on the weak entry) |
| 7 | Rc2_Events | `Rc2_Events.derive … extraction … sha256 H p1 syscall` | extraction | A0 |
| 8 | CPH_Protection | `CPH_Protection.derive … extraction … game data1 state1 final1 post1 accepted1` | game, accepted1 | TX1 + game (d) |
| 9 | CPH_Trace | `CPH_Trace.derive game` | game | game (d): A5 with G2 and the G1a weak entry |
| 10 | CPH_Recorder | `CPH_Recorder.physical … extraction … game sha256 H p1 syscall` | game, extraction | game (d) + A0 |
| 11 | S6N_Installation | `S6N_Installation.facts cfg` (FJp_Observations) | configuration | none needed |

Ten of the eleven conjuncts are therefore Root0-free at the top. They follow from extraction at the models (A0), `accepted1` (A3, which TAS already derives without Root0), game (A5 with G2), queries and retained binders. Conjunct 4 is the only one that needs `accepted2`.

### 1.2 Why the event cannot absorb Outcome

The premise of the brief's case (a) fails, because the charged event is not the whole of Outcome. `FJv_DResult.Outcome` (RPx_FJv_DBoundCaller.lean:111) is

```
∃ f s outer pre middle fs ss run tx2,
  P2P_Origin.Fact … program (e2.second secondSizes) data2 slot s ∧
  Cons_Native.Calls … s.pub s.proof s.checkpoint tx2 ∧
  TxS_Encoding.Facts run H ∧ Rc2_Base.Outcome … post2 … ∧ NP6_Constructors.Contents … ∧
  … ∧ (∃ version, … version.key = (e2.handles 6).1 ∧ …) ∧ … ∧
  P6C_OnCuts.SafeBatches … f s ∧ P6C_FullBoundary.Facts … f s ∧
  (bad ∨ P2P_Acceptance.Facts … ∧ P2P_Acceptance.Nonrejecting … ∧ FJv_DBoundCaller.Outcome …)
```

with `bad :=` the charged `BinRawByteCollisionTargets.event … (Q0+Q1+2965) …`. Only the last conjunct carries the event. The TX2 cut `s`, its origin fact on `e2.second secondSizes`, and the cohort reader success `Cons_Native.Calls` at `s` are facts about the model's TX2 run. The headline obtains them from `accepted2` (TCK §2.3: `S2W_NativeConsolidation.cuts_of_acceptance` rewrites `extraction.stage2` into `accepted2`). At the actual code, the rows give that model fact only on Root0 inputs. Where Root0 fails, the cohort reader fixes the root from proof[16..48] while the native resume reads checkpoint[112..144], so `Cons_Native.Calls` is not expected to hold. `Event → Outcome` is therefore unavailable, and the exact shape `Bound ∧ Concl` cannot be reached by placing the event inside Outcome. `TFM.exact_iff_event_gives_outcome` records this gap: the exact shape follows if and only if that implication is supplied.

### 1.3 What the top can conclude (compiled)

`TFM_TopExact.lean`, theorem `RSL.TFM.top_split`, has the same hypotheses as TAS `top` plus `sp : Split S`. It concludes

```
S.Bound c m1 m2 ∧ sp.Rest c m1 m2 ∧ (sp.Outcome c m1 m2 ∨ S.Event c m1)
```

where `Rest` is conjuncts 1–3 and 5–11 and `Outcome` is conjunct 4. `Split` adds two host fields. `concl_iff` is a propositional reassociation of the eleven-fold conjunction. `rest` is the Root0-free sub-lemma `Extraction → Accepted1 → Game → Queries → Rest`, and its host proof is exactly the branch terms in the table, none of which takes `accepted2`. The theorem is strictly stronger than TAS `top` (`top_split_to_top`), and off the event it is the exact headline shape (`top_split_exact_off_event`).

Compile record (TFM_COMPILE.tsv): `lake env lean` on the single file against the RSL_/TCK_/TAS_ oleans; exit 0, wall 0.29 s, peak RSS 430,587,904 bytes, swaps 0, sha256 e71fcaf9371435f467f32f3e340f72433589d5c72286b2ea03e3afde8815e3e7, Lean 4.31.0. `#print axioms`: `top_split` uses [propext, Classical.choice, Quot.sound], the same as TAS `top`. The three corollaries and `Alloc.reserve_true`/`allocator_part` use no axioms, and `Alloc.reserve_false` uses [propext]. There is no sorry, no axiom declaration and no Root0 hypothesis. RSL_ was rebuilt locally from the merged sources first; every module exited 0 below 0.7 GB.

### 1.4 Does the disjunction cost anything for 100-bit per-attempt soundness?

It does, unless the event is charged a second time or re-targeted. The derivation follows.

1. `failureModel runtime ≤ total(Q)` is `FJp_Residual.numeric`. Its proof adds `F3T_ModelClaims.failure_bound` (≤ `StartChargeNumeric.totalBound Q`) to the `accountLoss Q` term from `FJp_Mass.bounded`, and `F3T_Combined.arithmetic` gives `totalBound Q + accountLoss Q = total Q`. The `accountLoss` summand is consumed by `FJp_Mass` for the event `E_rec := BinRawByteCollisionTargets.event iv (Q+2965)` on `Hiq_RecordedJoint.program (ARX_LocalCharge.bounded (ART_PartialAccount.account cfg hashv copy allocator verifier a) Q) ARQ_Observer.project (ARQ_Observer.select cfg verifier)`. That is the adversary's own account run with an output-dependent selection.
2. The top's Event is `E_head :=` the same predicate at the same `Q+2965`, on `Hiq_RecordedJoint.program (F3X_Account.program cfg hashv P) F3X_Projection.project (fun _ => P2P_NativeSelection.pair (sdk cfg) verifier e1 e2 data2 slot)`. The source program and projection differ, and the selection is a constant fixed by the deployed pair. Its mass is bounded by conjunct 5a, `F3Y_AccountMass.Claims` (`F3T_AccountCharge.mass … ≤ accountLoss Q`), which is a separate inequality, not the summand already used in step 1. I found no theorem identifying E_head with E_rec or including one in the other.
3. With native := model, an actual TX2 acceptance on a non-Root0 input need not lie in the model runtime's admitted image, because the model wrapper may reject. Such a world adds nothing to `failureModel`, and only the event branch covers it. The adopted headline avoided this only through the universally quantified `extraction.stage2` at the actual code, which TCK §2.3 found unsupported off Root0.
4. Per world H, `top_split` gives `¬Outcome(H) → E_head(H)`. Hence `Pr_H[¬Concl] ≤ Pr_H[E_head] ≤ accountLoss(Q)`, and the deployed per-attempt figure is `failureModel + Pr[E_head] ≤ total(Q) + accountLoss(Q)`, not `total(Q)`.
5. Numerically (exact rationals, B = 15/2^109), `total(Q) + accountLoss(Q) ≤ (Q+1)·2^-100` holds for all `Q ≤ 4925986828297653200597000880669438074876558273` (about 2^151.79). That is two thirds of the current `maxQueries = 7388980242446479800895501321004157112314840375` (about 2^152.37, which the same computation reproduces exactly). The Q = 0 margin stays positive: `2^-108 − 6·(1161² + 2·2965²)/2^256 − 2^-126 − 2^-454 > 0`.
6. A further caveat applies. `F3T_AccountCharge.bound` is stated for a fixed selection. If the deployed pair `(e1, e2, data2, slot)` is chosen adaptively after oracle queries, the fixed-selection bound does not by itself bound `Pr_H` with an H-dependent pair. The adaptive E_rec has no such problem. The adopted headline's Outcome event shares this caveat, but in the top form E_head carries the TX2 acceptance, so the caveat becomes load-bearing.

So the disjunctive form loses nothing on worlds outside E_head, where it is the exact shape. On E_head worlds it loses Outcome, and the per-attempt number must charge Pr[E_head] explicitly. The clean repair is to re-target the case-split event to E_rec, which is already charged inside `failureModel`. Then the number stays `total(Q)` and the range stays `maxQueries`. Whether NMF′ can conclude E_rec at the actual run is open, because it requires relating the deployed pair to the adversary's run at H. The memo sets out the options.

## 2. Question 2: ALLOC

`S2W_D189Wrappers.Allocator A` has two data fields, `allocate : A → Nat → Result A` and `cleanup : A → Result A`, and no proposition. Unfolding `first`/`second`, `accepted1` holds exactly when (i) `reserve allocator (admittedSizes e1 3 firstSizes) state1 = ok m` for some `m`, (ii) the native call returns `.Ok saved`, (iii) `copy` returns `.returned written` with `post1 = release written …`, and (iv) `allocator.cleanup m = ok final1`. `accepted2` holds exactly when the same is true with 7 accounts, `secondSizes`, `state2`, `final2` and `post2 = e2.heap`. Game (d) uses the allocator in every recorded stage1 invocation (`Hir_Call.firstEffect` commits only on `ok (.Ok …)` from `first … call.state`). ASQ8 and rejected invocations are allocator-independent at the `Step` level, since `Step` keeps only the store and the event.

**The allocator facts are not supplied by the binder or by any trust row.** The binder carries no success proposition. The trust inventory says so explicitly (TRUST-INVENTORY-APPENDIX-DRAFT-20261027.md lines 71–72: "no success or account-access proposition"; TRUST-AUDIT row L191 / `Allocator`: "No Prop field guaranteeing success … Actual-runtime association remains separate"; PREMISE-LEDGER L191: "no automatic concrete history instance"). `accepted1/2` are class G success conditioning, to be "instantiated from the actual run" (L083/L084). With `allocator`, `state1`, `final1`, … left universally quantified, (i)/(iv) and the per-invocation agreement for game (d) are missing. RSL does not supply them either, because `Spec.alloc` carries no state (ruling (bl)(3)).

**They are provable without new trust if the top instantiates the allocator binders.** `allocator`, `A`, `state1`, `final1`, `state2` and `final2` are universally quantified headline binders, like `native1/2`. Take `A := Bool` and the abort-indicator allocator `allocate b _ := if b then ok b else fail` and `cleanup b := if b then ok b else fail`. Put `state1 = final1 = state2 = final2 := true`, and set each recorded invocation's `call.state` to whether that invocation completed without an allocation abort. Then (i)/(iv) hold by `reserve_true`/`cleanup_true` (compiled in `TFM_TopExact.lean`, section ALLOC, on a verbatim transcription of `reserve`/`thenResult`; the host proof is the same induction). An aborted stage1 invocation is modelled by `false`: its wrapper fails before the native call, so the step rolls back with an unchanged store, as the runtime does. The correspondence uses only facts already in scope:
- RSL models every allocation failure as `Exit.abort` (RSL_INDEX "Aborts"), so the returned-Ok selected occurrences (`ok1`, `ok2`) had no allocation failure;
- an allocation abort rolls back the transaction (C3-BIN 2026-10-23 02:40, inside the existing L191 runtime trust);
- the per-invocation abort status belongs to the physical trace association that `TraceRep` already carries.

The instance does not restrict the attacker. The adversary picks `state : A` in `GExq_AccountExperiment.FirstInputs`, so with `Bool` it may pick `true` (every allocation succeeds), and the numeric bound holds for every allocator. Allocation failure only aborts and never yields acceptance. The smallest statement NNE_ must then deliver, alongside A3/A4/A5, is: under `allocator := abortIndicator`, for every recorded stage1 invocation, `call.state = true` iff the actual invocation did not abort on allocation, and `call.state = true` at the two selected occurrences. This is Lean work for NNE_, not trust.

If the lead prefers to keep `allocator` universal, the missing fact becomes an actual-allocator association row (a runtime-class trust row: the binder is the runtime's private allocator, and its reserve/cleanup outcomes equal the runtime's). That would be a trust addition. The 2026-11-04 runtime-trust decision lets the lead add such a row and report it, but it is unnecessary given the instance above. My recommendation is the instance, recorded as a lead decision because it instantiates a universal binder and changes no adopted statement. The memo lists it for visibility.

## 3. What goes to the owner

One item goes to the owner: the top statement replaces the headline's conjunct 4 by `Outcome ∨ Event`, which changes the adopted headline's shape. The effect on the per-attempt number is either a second account charge (range ×2/3) or an open re-targeting obligation. See TFM_OWNER_MEMO.md. ALLOC needs no owner decision.

## 4. Handoff

- Established: `RSL.TFM.top_split` (compiled, TAS form), its corollaries, and `RSL.TFM.Alloc.*`. Ten headline conjuncts are Root0-free, and the source term for each is listed in §1.1.
- Discharged: none. Retained: everything TAS retains. Added: host obligations `Split.rest` (re-assembly of existing CLOSED terms, no `accepted2`) and `Split.concl_iff` (propositional). For NNE_, the ALLOC correspondence under the abort-indicator instance.
- Validation run: local RSL_ rebuild (20 modules), the TAS_ chain, and the TFM_ single file. No package or manifest replay. Numeric edges were computed with exact rationals in Python. They are not Lean-checked.
- Next deliverable: the owner's choice in TFM_OWNER_MEMO.md. Then either a Lean range lemma for `total + accountLoss` (option A) or an NNC_ amendment that re-targets the case-split event to E_rec (option B).
