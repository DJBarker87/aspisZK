/-
EVB_EventB: feasibility of option B (re-target the case-split event to E_rec).

Target not yet established.  Core Lean plus RSL_/TCK_/TAS_/TFM_ only.  No sorry,
no axiom declaration, no Root0 hypothesis, no hash-injectivity premise.

Finding (EVB_REPORT.md).  E_rec is the charged event of `FJp_Mass.bounded`:
  BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q0+Q1+2965)
    (eval H (Hiq_RecordedJoint.program
      (ARX_LocalCharge.bounded (ART_PartialAccount.account cfg hashv copy allocator
         CPH_Program.verifier a) (Q0+Q1))
      ARQ_Observer.project (ARQ_Observer.select cfg CPH_Program.verifier)))
The NNC_ fold (NNC_BindingRoot.root0_or_existing_collision) is generic in the
source program and projection, but its selector is the constant
`fun _ => P2P_NativeSelection.pair ops id e1 e2 data2 slot`.  Its proof uses the
selector only at the source output, through `P2P_Charge.binding_or_collision`.
So the same proof concludes `Root0 ∨ E_rec` as soon as the selector of the
adversary's own run returns the deployed pair at H (`SelectsPair`, section 1).

`SelectsPair` follows from TX1-only facts plus the relation `Realizes`
(the deployed pair is the adversary's run at the actual oracle H).  No
headline binder supplies `Realizes` or lets it be proved: `a` occurs in the
headline only in `queries` and in the let-bound `P`/`runtime`; `game` and
`RuntimePersistence` mention `p t u e1 e2`, never `a`.  B therefore needs
`Realizes` as a new hypothesis of the top (an owner decision on the statement).
-/
import TFM_TopExact
set_option autoImplicit false

namespace RSL.EVB
open RSL.TAS RSL.TFM
open TX2_241 (V2Lib Dom064)
open TX1_345 (S1Lib)

/-! ## 1. The selection core

Abstract form of the NNC_ fold.  `Coll sel` stands for
`BinRawByteCollisionTargets.event … (Hiq_RecordedJoint.program source project sel)`
at H, `binding` for `P2P_Charge.binding_or_collision source project sel Q budget H`,
and `transport` for `NNC_SourceCuts.on_cuts` + `NNC_BindingRoot.root0_of_binding`
(P2Prime at the deployed pair's bytes gives Root0).  Only `selects` depends on
which selector is used.  For E_head (`sel := fun _ => pair`) it is `rfl`; for
E_rec (`sel := ARQ_Observer.select cfg verifier`) it is the host lemma
`RecSelect.selects` below. -/
theorem core {Out Pair : Type} (sel : Out → Pair) (out : Out) (pair : Pair)
    (Coll : (Out → Pair) → Prop) (P2Prime : Pair → Prop) (Root0 : Prop)
    (binding : Coll sel ∨ P2Prime (sel out)) (selects : sel out = pair)
    (transport : P2Prime pair → Root0) : Root0 ∨ Coll sel := by
  rcases binding with bad | good
  · exact Or.inr bad
  · rw [selects] at good
    exact Or.inl (transport good)

/-- The existing NMF′ (E_head) is the constant-selector instance of `core`. -/
theorem core_head {Out Pair : Type} (out : Out) (pair : Pair)
    (Coll : (Out → Pair) → Prop) (P2Prime : Pair → Prop) (Root0 : Prop)
    (binding : Coll (fun _ => pair) ∨ P2Prime pair)
    (transport : P2Prime pair → Root0) : Root0 ∨ Coll (fun _ => pair) :=
  core (fun _ => pair) out pair Coll P2Prime Root0 binding rfl transport

/-! ## 2. Selector transcription

Verbatim transcription (not an import) of `GExq_AccountExperiment.FirstInputs`,
`SecondInputs`, `Outcome`, `Hiq_ByteSelection.select` and
`P2P_NativeSelection.pair`, with the byte readers `account`/`public2`, the
account views `entry.first`/`entry.second secondSizes` and the reply types
left abstract.  On an outcome whose TX2 branch was reached with inputs
`⟨e2, data2, slot, _⟩` after a first input with entry `e1`, the two selectors
agree by `rfl`.  On an outcome whose TX1 reply was not `.ok (.Ok …)`, the TX2
half of `select` is `⟨[], []⟩`, so `SelectsPair` needs the adversary's run to
reach TX2: that is where accepted1 at the model, A0 extraction and hash
agreement (p1, syscall) enter. -/
namespace Sel

abbrev Bytes := List UInt8

structure FirstInputs (E Dt A : Type) where
  entry : E
  data : Dt
  state : A

structure SecondInputs (E Dt Sl A : Type) where
  entry : E
  data : Dt
  slot : Sl
  state : A

abbrev Outcome (E Dt Sl A R1 R2 : Type) :=
  FirstInputs E Dt A × R1 × Option (SecondInputs E Dt Sl A × R2)

variable {E Dt Sl A R1 R2 Acc : Type}
  (account : Acc → Nat → Bytes) (first second : E → Acc)
  (public2 : Acc → Dt → Sl → Bytes)

/-- `Hiq_ByteSelection.select ops id`. -/
def select (out : Outcome E Dt Sl A R1 R2) : (Bytes × Bytes) × (Bytes × Bytes) :=
  (((account (first out.1.entry) 0).drop 688, account (first out.1.entry) 1),
   match out.2.2 with
   | none => ([], [])
   | some (next, _) => ((account (second next.entry) 0).drop 688,
       public2 (second next.entry) next.data next.slot))

/-- `P2P_NativeSelection.pair ops id e1 e2 data2 slot`. -/
def pair (e1 e2 : E) (data2 : Dt) (slot : Sl) : (Bytes × Bytes) × (Bytes × Bytes) :=
  (((account (first e1) 0).drop 688, account (first e1) 1),
   ((account (second e2) 0).drop 688, public2 (second e2) data2 slot))

theorem select_realized (i : FirstInputs E Dt A) (r : R1) (j : SecondInputs E Dt Sl A) (o : R2) :
    select account first second public2 (i, r, some (j, o)) =
      pair account first second public2 i.entry j.entry j.data j.slot := rfl

theorem select_unreached (i : FirstInputs E Dt A) (r : R1) :
    (select account first second public2 ((i, r, none) : Outcome E Dt Sl A R1 R2)).2 = ([], []) := rfl

end Sel

/-! ## 3. Option B interfaces (TAS stand-in form) -/

section B
variable (S : Sig) (L : PoolLib) (D : DeployedIds) (V0 : V2Lib) (VL : VLib)
  (P : PreparedNew VL) (C : S1Lib VL) (I : Impl L V0 VL)

/-- Option B stand-ins.  Each field names the exact host term. -/
structure RecSig where
  /-- NEW top hypothesis (owner decision): the deployed pair is the adversary's
  run at the actual oracle H.  Host, with `i := ⟨e1, data1, state1⟩`:
    `(eval H a.first).2 = i ∧
     (eval H (a.second i saved post1 final1)).2 = ⟨e2, data2, slot, state2⟩`
  (`GExq_AccountExperiment.FirstInputs/SecondInputs`, `SCE_Experiment.Adversary`).
  It is the TX1 half of `ARS_Coverage.SupportedEntry` (its fields `admission1`,
  `accepted1`, `game` already use `(eval H a.first).2.entry` and
  `(eval H (a.second … saved post1 final1)).2.entry` as e1/e2) without
  `accepted2`. -/
  Realizes : S.Ctx → Prop
  /-- E_rec, verbatim from `FJp_Mass.bounded` (see header).  It takes no
  `First`/`Second` argument: `ART_PartialAccount.account` runs the source
  syntax, not `native1/2`. -/
  EventRec : S.Ctx → Prop
  /-- `ARQ_Observer.select cfg CPH_Program.verifier
     (eval H (ARX_LocalCharge.bounded (ART_PartialAccount.account cfg hashv copy
        allocator CPH_Program.verifier a) (Q0+Q1))).2 =
   P2P_NativeSelection.pair (DrvC_Installation.sdk cfg) CPH_Program.verifier e1 e2 data2 slot`. -/
  SelectsPair : S.Ctx → Prop

/-- Host lemma, TX1-only (no `accepted2`, no Root0, no TX2 model fact).
Proof plan: `ART_WrapperExact.execution` with Agrees from `p1`/`syscall`, and
`ARU_WrapperSource.first` from extraction and accepted1, give the account run's
first reply `ok (.Ok (saved, post1, final1))` (the TX1 halves of
`ARU_SourceResults.accepted`/`ARV_FirstPartial.accepted` with the `At` record
replaced by `Realizes`).  Then `ARW_Induced.issued = work` (as
`ARW_AdmittedQueries.admitted`), `ARW_LocalBudget.issued` and `queries` give
the log budget `≤ Q0+Q1+1921`, `ARX_LocalCharge.exact` removes the cap, and
`Sel.select_realized` closes the equation by `rfl`. -/
structure RecSelect (R : RecSig S) where
  selects : ∀ c, S.Exhibited c → S.Extraction c (S.model1 c) (S.model2 c) →
    S.Accepted1 c (S.model1 c) → S.Queries c (S.model1 c) → R.Realizes c → R.SelectsPair c

/-- NNC_ amendment (NMF′-B).  Identical premises to `NNC_NMFPrime.root0_or_event`
plus `SelectsPair`; the event is E_rec.  Host proof: the NNC_ fold with the
selector generalised (section 1, `core`), source := the capped account run,
project := `ARQ_Observer.project`, binding := `ARX_LocalCharge.binding` (or
`P2P_Charge.binding_or_collision` on the capped source with
`ARX_LocalCharge.budget`). -/
structure NNC_NMFPrimeB (g : NNC_G1a S L V0 VL I) (R : RecSig S) where
  root0_or_rec : ∀ c, S.Exhibited c →
    (∀ a s env, TX2_213.Ref L D (lib V0 (fun _ _ => True) g.w) (TX1_344.asStage1 VL P C)
      a s env (I.entry a s env)) →
    (∃ s', (I.entry (S.args2 c) (S.state2 c) (S.env2 c)).exit = .ret (.ok (), s')) →
    S.Accepted1 c (S.model1 c) →
    S.Game c (S.model1 c) (S.model2 c) →
    S.Extraction c (S.model1 c) (S.model2 c) →
    S.Queries c (S.model1 c) →
    R.SelectsPair c →
    S.Root0Native c ∨ R.EventRec c

end B

/-- The B top: TFM `top_split` with the case-split event re-targeted to E_rec.
Extra hypotheses relative to `top_split`: `R`, `rs`, `nmfB` (interfaces) and
`realizes` (the new top binder).  `nmf`/`cs` are no longer needed. -/
theorem top_splitB (S : Sig) (L : PoolLib) (D : DeployedIds) (V0 : V2Lib) (VL : VLib)
    (P : PreparedNew VL) (C : S1Lib VL) (I : Impl L V0 VL)
    (sp : Split S) (hl : Headline S) (a0 : A0_Digest S)
    (nmm : NMM_Roots L D V0 VL I) (nmx : NMX_Root L D V0 VL I) (nms : NMS_Roots L D V0 VL I)
    (nmv : NMV_Roots L D V0 VL P C I) (nmw : NMW_Roots L D V0 VL P C I)
    (nmt : NMT_Roots L V0 VL P C I) (nmp : NMP_Roots L V0 VL P I) (nmo : NMO_Root L V0 VL I)
    (nmn : NMN_Root L V0 VL I)
    (g1a : NNC_G1a S L V0 VL I) (R : RecSig S) (rs : RecSelect S R)
    (nmfB : NNC_NMFPrimeB S L D V0 VL P C I g1a R) (r0 : NNC_R0Rep S V0)
    (a1 : NND_A1 S VL P C) (a2 : NND_A2 S L D V0)
    (a3 : NNE_A3 S VL P C) (a4 : NNE_A4 S L D V0) (a5 : NNE_A5 S L V0 VL P C I)
    (er : NNE_EntryRep S L V0 VL I)
    (c : S.Ctx) (hx : S.Exhibited c) (queries : S.Queries c (S.model1 c))
    (frame : S.GameFrame c) (trace : S.TraceRep c I.entry)
    (realizes : R.Realizes c)
    (ok1 : ∃ s', (I.entry (S.args1 c) (S.state1 c) (S.env1 c)).exit = .ret (.ok (), s'))
    (out1 : S.Out1 c (I.entry (S.args1 c) (S.state1 c) (S.env1 c)))
    (ok2 : ∃ s', (I.entry (S.args2 c) (S.state2 c) (S.env2 c)).exit = .ret (.ok (), s'))
    (out2 : S.Out2 c (I.entry (S.args2 c) (S.state2 c) (S.env2 c))) :
    S.Bound c (S.model1 c) (S.model2 c) ∧
      sp.Rest c (S.model1 c) (S.model2 c) ∧
      (sp.Outcome c (S.model1 c) (S.model2 c) ∨ R.EventRec c) := by
  have ext := a0.extraction c hx
  have bound := hl.numeric c _ _ ext queries
  have weak := weakEntry nmm nmx nms nmv nmw nmt nmp nmo g1a
  have stage1Ref : ∀ a s env, TX2_221.stage1Route a.data = true →
      TX1_344.Ref VL P C a s env (I.entry a s env) :=
    fun a s env h1 => ref213_stage1 h1 (weak a s env)
  have reject : ∀ a s env, TX2_221.admitted a.data = false →
      I.entry a s env = ⟨.ret (.error .invalidInstructionData, s), []⟩ :=
    fun a s env hn => ref213_reject hn (weak a s env)
  have recd := a5.recorded c a1 hx stage1Ref (asq8Frame nmm nmx nms nmv nmw nmt nmp nmo g1a)
    reject trace
  have game := S.mkGame c _ _ frame recd.1 recd.2
  have acc1 := a3.accepted1 c _ a1 hx (stage1Ref _ _ _ (er.route1 c frame trace)) ok1 out1
  have rest := sp.rest c _ _ ext acc1 game queries
  have sel := rs.selects c hx ext acc1 queries realizes
  refine ⟨bound, rest, ?_⟩
  rcases nmfB.root0_or_rec c hx weak ok2 acc1 game ext queries sel with root0 | ev
  · have ref240 := canonicalRef240 nmm nmx nms nmv nmw nmt nmp nmo nmn
      (S.args2 c) (S.state2 c) (S.env2 c) (er.route2 c frame trace) (domain240_of_rep r0 c root0)
    have acc2 := a4.accepted2 c _ a2 hx ref240 ok2 out2
    exact Or.inl ((sp.concl_iff c _ _).mp (hl.deployed c _ _ ext acc1 acc2 game queries)).2
  · exact Or.inr ev

/-! ## 3b. Full B: the inner `bad` of Outcome re-targeted as well

`FJv_DResult.Outcome`'s last conjunct is `bad ∨ P2P_Acceptance.Facts … ∧ …`, with
`bad := E_head` in the adopted statement.  On the Root0 arm, `top_splitB` still
returns the adopted Outcome, whose inner `bad` is E_head and so keeps the
fixed-selection caveat.  The inner event is produced in exactly one place,
`FJv_DRelease.remove` line 90, by
`P2P_Charge.binding_or_collision account project (fun _ => pair …) Q budget H`;
`remove` is already generic in `account`/`project`.  `OutcomeRec` is the same
Outcome with `bad := E_rec`; `HeadlineB.outcomeRec` is the host variant
`remove'` (selector generalised, plus `selects`), instantiated by a copy of
`FJv_DNativeAccepted.accepted` at the capped account run, `ARQ_Observer.project`,
`ARQ_Observer.select cfg verifier` and `ARX_LocalCharge.budget`. -/
structure HeadlineB (S : Sig) (R : RecSig S) where
  OutcomeRec : S.Ctx → S.First → S.Second → Prop
  outcomeRec : ∀ c n1 n2, S.Extraction c n1 n2 → S.Accepted1 c n1 → S.Accepted2 c n2 →
    S.Game c n1 n2 → S.Queries c n1 → R.SelectsPair c → OutcomeRec c n1 n2

theorem top_splitB_full (S : Sig) (L : PoolLib) (D : DeployedIds) (V0 : V2Lib) (VL : VLib)
    (P : PreparedNew VL) (C : S1Lib VL) (I : Impl L V0 VL)
    (sp : Split S) (hl : Headline S) (a0 : A0_Digest S)
    (nmm : NMM_Roots L D V0 VL I) (nmx : NMX_Root L D V0 VL I) (nms : NMS_Roots L D V0 VL I)
    (nmv : NMV_Roots L D V0 VL P C I) (nmw : NMW_Roots L D V0 VL P C I)
    (nmt : NMT_Roots L V0 VL P C I) (nmp : NMP_Roots L V0 VL P I) (nmo : NMO_Root L V0 VL I)
    (nmn : NMN_Root L V0 VL I)
    (g1a : NNC_G1a S L V0 VL I) (R : RecSig S) (rs : RecSelect S R) (hb : HeadlineB S R)
    (nmfB : NNC_NMFPrimeB S L D V0 VL P C I g1a R) (r0 : NNC_R0Rep S V0)
    (a1 : NND_A1 S VL P C) (a2 : NND_A2 S L D V0)
    (a3 : NNE_A3 S VL P C) (a4 : NNE_A4 S L D V0) (a5 : NNE_A5 S L V0 VL P C I)
    (er : NNE_EntryRep S L V0 VL I)
    (c : S.Ctx) (hx : S.Exhibited c) (queries : S.Queries c (S.model1 c))
    (frame : S.GameFrame c) (trace : S.TraceRep c I.entry)
    (realizes : R.Realizes c)
    (ok1 : ∃ s', (I.entry (S.args1 c) (S.state1 c) (S.env1 c)).exit = .ret (.ok (), s'))
    (out1 : S.Out1 c (I.entry (S.args1 c) (S.state1 c) (S.env1 c)))
    (ok2 : ∃ s', (I.entry (S.args2 c) (S.state2 c) (S.env2 c)).exit = .ret (.ok (), s'))
    (out2 : S.Out2 c (I.entry (S.args2 c) (S.state2 c) (S.env2 c))) :
    S.Bound c (S.model1 c) (S.model2 c) ∧
      sp.Rest c (S.model1 c) (S.model2 c) ∧
      (hb.OutcomeRec c (S.model1 c) (S.model2 c) ∨ R.EventRec c) := by
  have ext := a0.extraction c hx
  have bound := hl.numeric c _ _ ext queries
  have weak := weakEntry nmm nmx nms nmv nmw nmt nmp nmo g1a
  have stage1Ref : ∀ a s env, TX2_221.stage1Route a.data = true →
      TX1_344.Ref VL P C a s env (I.entry a s env) :=
    fun a s env h1 => ref213_stage1 h1 (weak a s env)
  have reject : ∀ a s env, TX2_221.admitted a.data = false →
      I.entry a s env = ⟨.ret (.error .invalidInstructionData, s), []⟩ :=
    fun a s env hn => ref213_reject hn (weak a s env)
  have recd := a5.recorded c a1 hx stage1Ref (asq8Frame nmm nmx nms nmv nmw nmt nmp nmo g1a)
    reject trace
  have game := S.mkGame c _ _ frame recd.1 recd.2
  have acc1 := a3.accepted1 c _ a1 hx (stage1Ref _ _ _ (er.route1 c frame trace)) ok1 out1
  have rest := sp.rest c _ _ ext acc1 game queries
  have sel := rs.selects c hx ext acc1 queries realizes
  refine ⟨bound, rest, ?_⟩
  rcases nmfB.root0_or_rec c hx weak ok2 acc1 game ext queries sel with root0 | ev
  · have ref240 := canonicalRef240 nmm nmx nms nmv nmw nmt nmp nmo nmn
      (S.args2 c) (S.state2 c) (S.env2 c) (er.route2 c frame trace) (domain240_of_rep r0 c root0)
    have acc2 := a4.accepted2 c _ a2 hx ref240 ok2 out2
    exact Or.inl (hb.outcomeRec c _ _ ext acc1 acc2 game queries sel)
  · exact Or.inr ev

/-! ## 4. No second charge

Per world H, write `r` for `F3T_Runtime.runtimeMass (eval H runtime)`, `m` for
`failureMass (eval H model)` and `e` for the indicator of E_rec at H.
`FJp_Mass.bounded` proves `r ≤ m + e` (`each`) for every H and averages it with
`F3U_Averaging.charge`; `F3T_AccountCharge.bound` bounds the mean of `e` by
`accountLoss`.  With `top_splitB`, ¬Outcome at H gives E_rec at H.  The
deployed per-world loss `max r (indicator ¬Outcome)` then satisfies the SAME
pointwise inequality, so its mean is at most `total (Q0+Q1)`: E_rec is charged
once.  (The averaging step for `max r _` is a host restatement of
`F3U_Averaging.charge`; it is not compiled here.) -/
theorem no_second_charge (r m : Rat) (E notOutcome : Prop) [Decidable E] [Decidable notOutcome]
    (hm : 0 ≤ m) (each : r ≤ m + (if E then 1 else 0)) (split : notOutcome → E) :
    max r (if notOutcome then 1 else 0) ≤ m + (if E then 1 else 0) := by
  have maxLe : ∀ x y z : Rat, x ≤ z → y ≤ z → max x y ≤ z := by
    intro x y z h1 h2
    rw [Rat.max_def]
    split <;> assumption
  by_cases he : E
  · apply maxLe _ _ _ each
    rw [if_pos he]
    by_cases hn : notOutcome
    · rw [if_pos hn]
      have := (Rat.add_le_add_right (c := 1)).mpr hm
      rwa [Rat.zero_add] at this
    · rw [if_neg hn]
      have := (Rat.add_le_add_left (c := m)).mpr (show (0:Rat) ≤ 1 by decide)
      rw [Rat.add_zero] at this
      exact Rat.le_trans hm this
  · have hn : ¬ notOutcome := fun h => he (split h)
    rw [if_neg hn]
    apply maxLe _ _ _ each
    rw [if_neg he, Rat.add_zero]
    exact hm

#print axioms core
#print axioms core_head
#print axioms Sel.select_realized
#print axioms Sel.select_unreached
#print axioms top_splitB
#print axioms top_splitB_full
#print axioms no_second_charge

end RSL.EVB
