import NPH_R22JoinCW
import NPH_R22Join094
import NID_ResumeFields
import NID_ResumeQuery
import NKE_ResumeWidth
import NFW_PowersDomain
import NFW_QueryResume
import NFS_CallerDomains
import NFS_AccumDomain
import NFS_QueryInvariant
import Port4D_Round
import NIG_Slots
import SAG_DotClosed
import RPz7_FIn_WeightsInstall
import RPz7_FIn_Install
import NHE_DotBody

/-! NPH_ (R22, run of 2026-11-10 night, CW step 1): the CurrentWide (CW) contexts that
NPH_R22JoinCW left open, composed from producers along the reached tx2 body.
W is limbs ≤ P (NPH_R22Weak); WE is W on the Stage2 wide carrier (NPH_R22Callbacks).

Finish (tx2 only; VTop_Stages tx1 never calls op19):
- Producer. The finish Prepared p is the return of the tx2 resume
  (NJJ_Common.resume, op18 of tx2_common). Its success alone gives
  NID_ResumeFields.Domain p a (strict checkpoint decoders NJC_EReaderResults.naturalE:
  the Ok arm is guarded by CanonicalWide). The checkpoint width 1768 comes from the same
  success (NKE_ResumeWidth.checkpoint). No acceptance of a later call is used.
- `resume_alpha_W`: both alpha reads of the finish body return W values.
- `tx2_finish_round`: on the tx2 native finish (NIG_Slots.installed r, equal to
  finishRelationWithOps on Port3_FinishStage.release (IDa_Deployed.finish r) by
  Port4D_Round.parent_eq), each round's CW calls are ok with W outputs: the lhs add on
  successful field reads, mulM for every claim, and every Horner step of the polynomial on
  the read alpha.
- `kernel_slots`: the finish dot SAG_DotAdapter.kernel equals finish_query_dot on the same
  record with the add/mulM31/quarter slots replaced by ANY functions. So the dot executes
  no finishAdd/finishScale call, hence no CW kernel (its slots are field = finishField,
  pushDot/finishDot = the EbyK backend).
- Record builders finishArithmetic/finishCheckedArithmetic/finishConcreteField and
  NHE_DotBody.ops: their add slot is finishAdd (W-preserving, NPH_R22JoinCW.finishAdd_W),
  mulM31 is finishScale (ok for every input), field is finishField (producer).
- FIn_Install.finishOps and FIn_WeightsInstall.install: the four round slots are the
  deployed ones, so the round lemmas apply to them unchanged.

Query (tx2, the non-094 dictionary NJJ_Common.query = NHT_PacketOps.query
NJJ_QueryOps.concrete, executed as query_values on Dcon = NFS_QueryOps.installed
NJJ_QueryOps.concrete by NFW_QueryResume.tx2):
- `Reach`: the states of the tx2 query loop, from the resume state by successful steps.
- `reach_domain`: every reached state satisfies NFS_QueryInvariant.Domain (initial domain
  NID_ResumeQuery.domain, preserved by NFS_QueryInvariant.step on each successful step).
- `Dcon_values_canon`: the op0/op21 opening values of Dcon are canonical (SAQ_Decoder.read
  producer).
- `tx2_step_sites`: at every reached state, the circle call on alpha[0], the line call on
  alpha[1] and the three accumulate tail calls are ok with canonical/W outputs.
Standard axioms; no ops interface, merged module or closed-row statement is changed. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.NPH_R22JoinCW2
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1.NPH_R22Producers AspisR1.NPH_R22Callbacks
open AspisR1.NPH_R22Join094 AspisR1.NPH_R22JoinCW

/-! ### Producer: the tx2 resume -/

theorem ecanon_W (x : SAQ_WideABI.E) (h : NID_ResumeCanonical.ECanonical x) : WE x := by
  obtain ⟨⟨h1, h2, h3, h4⟩, ⟨h5, h6, h7, h8⟩⟩ := h
  exact ⟨⟨⟨Nat.le_of_lt h1, Nat.le_of_lt h2⟩, ⟨Nat.le_of_lt h3, Nat.le_of_lt h4⟩⟩,
    ⟨⟨Nat.le_of_lt h5, Nat.le_of_lt h6⟩, ⟨Nat.le_of_lt h7, Nat.le_of_lt h8⟩⟩⟩

theorem ecanon_canonE (x : SAQ_WideABI.E) (h : NID_ResumeCanonical.ECanonical x) :
    Port4C_QueryArithmetic.CanonE x := by
  obtain ⟨⟨h1, h2, h3, h4⟩, ⟨h5, h6, h7, h8⟩⟩ := h
  exact ⟨⟨h1, h2, h3, h4⟩, ⟨h5, h6, h7, h8⟩⟩

/-- The tx2 resume (op18 of tx2_common) alone gives the resumed Domain. -/
theorem entered_domain (reservation : NP6_StdModel.Reservation) {H : Type}
    (d : VTop_Stages.aspis_core.digest.Digest32 H) (ck proof pub : Slice U8) (hash : H)
    (p : verifier.Prepared) (a : verifier.Accumulator)
    (entered : NJJ_Common.resume reservation d ck proof pub .S2 hash = ok (.Ok (p,a))) :
    NID_ResumeFields.Domain p a ∧
    verifier.resumeWithOps (CheckpointBytes4Ops.ops (NJC_FilledClause.reserved reservation))
      (NJC_ResumeCalls.digest d) ck proof pub .S2 hash = ok (.Ok (p,a)) ∧
    ck.val.length = 1768 := by
  have size := NKE_ResumeWidth.checkpoint reservation d ck proof pub hash p a entered
  have e2 := entered
  unfold NJJ_Common.resume at e2
  rw [NJC_ResumeCalls.clause] at e2
  have same := NKE_ResumeDomain.action_ok _ _ e2
  change verifier.resumeWithOps (CheckpointBytes4Ops.ops (NJC_FilledClause.reserved reservation))
    (NJC_ResumeCalls.digest d) ck proof pub .S2 hash = ok (.Ok (p,a)) at same
  exact ⟨NID_ResumeFields.returned _ _ ck proof pub hash p a size same, same, size⟩

theorem alpha_read {p : verifier.Prepared} {w : SAQ_WideABI.E} (j : Usize) (hj : j.val < 2)
    (hw : Array.index_usize p.alpha j = ok w) : w ∈ p.alpha.val := by
  have hl : p.alpha.val.length = 2 := by first | exact p.alpha.property | simpa using p.alpha.property
  obtain ⟨t, ht, htv⟩ := WP.spec_imp_exists
    (Array.index_usize_spec p.alpha j (by first | scalar_tac | simp [hl]; omega | omega))
  have tw : t = w := Result.ok.inj (ht.symm.trans hw)
  subst tw
  have e : t = p.alpha.val[j.val]'(by rw [hl]; exact hj) := by
    first | (rw [htv]; rfl) | simpa using htv | (subst htv; rfl) | simp [htv]
  rw [e]; exact List.getElem_mem _

theorem resume_alpha_W {p : verifier.Prepared} {a : verifier.Accumulator}
    (d : NID_ResumeFields.Domain p a) (j : Usize) (hj : j.val < 2) (w : SAQ_WideABI.E)
    (hw : Array.index_usize p.alpha j = ok w) : WE w :=
  ecanon_W w (d.alpha w (alpha_read j hj hw))

theorem resume_alpha_canonE {p : verifier.Prepared} {a : verifier.Accumulator}
    (d : NID_ResumeFields.Domain p a) (j : Usize) (hj : j.val < 2) (w : SAQ_WideABI.E)
    (hw : Array.index_usize p.alpha j = ok w) : Port4C_QueryArithmetic.CanonE w :=
  ecanon_canonE w (d.alpha w (alpha_read j hj hw))

/-! ### Finish rounds on the tx2 native finish -/

/-- The tx2 native finish is finishRelationWithOps on the released deployed record. -/
theorem tx2_finish_body (r : NP6_StdModel.Reservation) (v : verifier.View) (p : verifier.Prepared)
    (a : verifier.Accumulator) (obs : Option (verifier.Phase → Result Unit)) :
    Port3_NativeFinishBody.verifier.finish_relation (NIG_Slots.installed r) v p a obs =
      AspisR1Stage2.Stage2Finish.verifier.finishRelationWithOps (Port3_FinishStage.release (IDa_Deployed.finish r)) v p a obs :=
  Port4D_Round.parent_eq _ v p a obs

/-- Every CW call of one finish round, on the round's actual alpha read. -/
theorem tx2_finish_round (r : NP6_StdModel.Reservation) {p : verifier.Prepared}
    {a : verifier.Accumulator} (d : NID_ResumeFields.Domain p a)
    (j : Usize) (hj : j.val < 2) (alpha : SAQ_WideABI.E)
    (hw : Array.index_usize p.alpha j = ok alpha) (poly : Slice U8) (claim : SAQ_WideABI.E) :
    (∀ we we1, (Port3_FinishStage.release (IDa_Deployed.finish r)).field poly 0#usize = ok we →
      (Port3_FinishStage.release (IDa_Deployed.finish r)).field poly 4#usize = ok we1 →
      ∃ lhs, (Port3_FinishStage.release (IDa_Deployed.finish r)).add we we1 = ok lhs ∧ WE lhs) ∧
    (∀ m, ∃ rhs, (Port3_FinishStage.release (IDa_Deployed.finish r)).mulM claim m = ok rhs) ∧
    (∀ (i : Usize) (acc : SAQ_WideABI.E), WE acc →
      ∃ t, AspisR1.FIn_ExtractInstall.arithmetic.mul acc alpha = ok t ∧ WE t ∧
        ∀ c, AspisR1.FIn_ExtractInstall.arithmetic.field poly i = ok c →
          ∃ acc', AspisR1.FIn_ExtractInstall.arithmetic.add t c = ok acc' ∧ WE acc') ∧
    ((∀ i : Usize, ∃ v, (Port3_FinishStage.release (IDa_Deployed.finish r)).field poly i = ok v) →
      ∃ z, (Port3_FinishStage.release (IDa_Deployed.finish r)).polynomial poly alpha = ok z ∧ WE z) := by
  have wa := resume_alpha_W d j hj alpha hw
  obtain ⟨s1, s2, s3⟩ := round_sites (Port3_FinishStage.release (IDa_Deployed.finish r))
    rfl rfl rfl rfl poly alpha claim
  exact ⟨s1, s2, fun i acc hacc => poly_step poly i acc alpha hacc wa, s3 wa⟩

/-- The same round statement, with the Domain taken from the tx2 resume success itself. -/
theorem tx2_finish_round_entered (reservation r : NP6_StdModel.Reservation) {H : Type}
    (dg : VTop_Stages.aspis_core.digest.Digest32 H) (ck proof pub : Slice U8) (hash : H)
    (p : verifier.Prepared) (a : verifier.Accumulator)
    (entered : NJJ_Common.resume reservation dg ck proof pub .S2 hash = ok (.Ok (p,a)))
    (j : Usize) (hj : j.val < 2) (alpha : SAQ_WideABI.E)
    (hw : Array.index_usize p.alpha j = ok alpha) (poly : Slice U8) :
    WE alpha ∧
    ∀ (i : Usize) (acc : SAQ_WideABI.E), WE acc →
      ∃ t, AspisR1.FIn_ExtractInstall.arithmetic.mul acc alpha = ok t ∧ WE t ∧
        ∀ c, AspisR1.FIn_ExtractInstall.arithmetic.field poly i = ok c →
          ∃ acc', AspisR1.FIn_ExtractInstall.arithmetic.add t c = ok acc' ∧ WE acc' := by
  have d := (entered_domain reservation dg ck proof pub hash p a entered).1
  have wa := resume_alpha_W d j hj alpha hw
  exact ⟨wa, fun i acc hacc => poly_step poly i acc alpha hacc wa⟩

/-- FIn_Install.finishOps and FIn_WeightsInstall.install carry the deployed round slots. -/
theorem finishOps_round_slots {W : Type} (seed : AspisR1Stage2.Stage2Finish.FinishOps W)
    (seed2 : AspisR1Stage2.Stage2Finish.FinishOps AspisR1.FIn_WeightsInstall.W) :
    (AspisR1.FIn_Install.finishOps seed).field = AspisR1.FIn_Primitives.field ∧
    (AspisR1.FIn_Install.finishOps seed).add = AspisR1.FIn_Primitives.add ∧
    (AspisR1.FIn_Install.finishOps seed).mulM = AspisR1.SAG_StageScale.mulM ∧
    (AspisR1.FIn_Install.finishOps seed).polynomial = AspisR1.FIn_ExtractInstall.polynomial ∧
    (AspisR1.FIn_WeightsInstall.install seed2).field = AspisR1.FIn_Primitives.field ∧
    (AspisR1.FIn_WeightsInstall.install seed2).add = AspisR1.FIn_Primitives.add ∧
    (AspisR1.FIn_WeightsInstall.install seed2).mulM = AspisR1.SAG_StageScale.mulM ∧
    (AspisR1.FIn_WeightsInstall.install seed2).polynomial = AspisR1.FIn_ExtractInstall.polynomial :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem finishOps_round_sites {W : Type} (seed : AspisR1Stage2.Stage2Finish.FinishOps W)
    (seed2 : AspisR1Stage2.Stage2Finish.FinishOps AspisR1.FIn_WeightsInstall.W)
    (poly : Slice U8) (alpha claim : SAQ_WideABI.E) :
    ((∀ we we1, (AspisR1.FIn_Install.finishOps seed).field poly 0#usize = ok we →
      (AspisR1.FIn_Install.finishOps seed).field poly 4#usize = ok we1 →
      ∃ lhs, (AspisR1.FIn_Install.finishOps seed).add we we1 = ok lhs ∧ WE lhs) ∧
    (∀ m, ∃ rhs, (AspisR1.FIn_Install.finishOps seed).mulM claim m = ok rhs) ∧
    (WE alpha → (∀ i : Usize, ∃ v, (AspisR1.FIn_Install.finishOps seed).field poly i = ok v) →
      ∃ z, (AspisR1.FIn_Install.finishOps seed).polynomial poly alpha = ok z ∧ WE z)) ∧
    ((∀ we we1, (AspisR1.FIn_WeightsInstall.install seed2).field poly 0#usize = ok we →
      (AspisR1.FIn_WeightsInstall.install seed2).field poly 4#usize = ok we1 →
      ∃ lhs, (AspisR1.FIn_WeightsInstall.install seed2).add we we1 = ok lhs ∧ WE lhs) ∧
    (∀ m, ∃ rhs, (AspisR1.FIn_WeightsInstall.install seed2).mulM claim m = ok rhs) ∧
    (WE alpha → (∀ i : Usize, ∃ v, (AspisR1.FIn_WeightsInstall.install seed2).field poly i = ok v) →
      ∃ z, (AspisR1.FIn_WeightsInstall.install seed2).polynomial poly alpha = ok z ∧ WE z)) :=
  ⟨round_sites _ rfl rfl rfl rfl poly alpha claim, round_sites _ rfl rfl rfl rfl poly alpha claim⟩

/-! ### The finish dot executes no CW call -/

theorem kernel_slots {W : Type} (ops : AspisR1FinishRelationCurrent.FinishOps W
      AspisR1FinishDotSourceABI.PushState)
    (fm : Slice U8) (ws : Slice AspisR1Stage2.Stage2Finish.K)
    (add : AspisR1FinishRelationCurrent.aspis_core.field.WideExact →
      AspisR1FinishRelationCurrent.aspis_core.field.WideExact →
      Result AspisR1FinishRelationCurrent.aspis_core.field.WideExact)
    (mulM31 : AspisR1FinishRelationCurrent.aspis_core.field.WideExact →
      AspisR1FinishRelationCurrent.aspis_core.field.M31 →
      Result AspisR1FinishRelationCurrent.aspis_core.field.WideExact)
    (quarter : Result AspisR1FinishRelationCurrent.aspis_core.field.M31) :
    AspisR1.SAG_DotAdapter.kernel ops fm ws =
      AspisR1FinishRelationCurrent.verifier.finish_query_dot
        (AspisR1FinishDotConcreteOps.withConcreteDot
          {AspisR1CurrentWide.Proof.finishConcreteField ops with
            add := add, mulM31 := mulM31, quarter := quarter}
          AspisR1EbyKPushDecodedProductUpdate.QRaw) fm
        (AspisR1.SAG_DotAdapter.mapSlice AspisR1.SAG_DotAdapter.toFinishQ ws) := rfl

/-! ### Record builders over finishAdd/finishScale -/

theorem finishScale_ok (x : AspisR1CurrentWide.Proof.FinishE) (s : U32) :
    ∃ z, AspisR1CurrentWide.Proof.finishScale x s = ok z := by
  obtain ⟨w, hw, _⟩ := CW_WideExact_mul_m31_weak (AspisR1CurrentWide.Proof.ofFinishE x) s
  exact ⟨AspisR1CurrentWide.Proof.toFinishE w,
    by simp only [AspisR1CurrentWide.Proof.finishScale, hw, bind_tc_ok]⟩

theorem finishConcreteField_slots {W D : Type} (ops : AspisR1FinishRelationCurrent.FinishOps W D) :
    (AspisR1CurrentWide.Proof.finishConcreteField ops).add = AspisR1CurrentWide.Proof.finishAdd ∧
    (AspisR1CurrentWide.Proof.finishConcreteField ops).mulM31 = AspisR1CurrentWide.Proof.finishScale ∧
    (AspisR1CurrentWide.Proof.finishConcreteField ops).field = AspisR1CurrentWide.Proof.finishField ∧
    (AspisR1CurrentWide.Proof.finishCheckedArithmetic ops).add = AspisR1CurrentWide.Proof.finishAdd ∧
    (AspisR1CurrentWide.Proof.finishCheckedArithmetic ops).mulM31 = AspisR1CurrentWide.Proof.finishScale ∧
    (AspisR1CurrentWide.Proof.finishArithmetic ops).add = AspisR1CurrentWide.Proof.finishAdd ∧
    (AspisR1CurrentWide.Proof.finishArithmetic ops).mulM31 = AspisR1CurrentWide.Proof.finishScale :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Record-level W statement: every slot of the three builders that calls a CW kernel maps
W inputs to ok W outputs (add), or is ok on every input (mulM31). -/
theorem finishConcreteField_W {W D : Type} (ops : AspisR1FinishRelationCurrent.FinishOps W D) :
    (∀ x y, CWW (AspisR1CurrentWide.Proof.ofFinishE x) → CWW (AspisR1CurrentWide.Proof.ofFinishE y) →
      ∃ z, (AspisR1CurrentWide.Proof.finishConcreteField ops).add x y = ok z ∧
        CWW (AspisR1CurrentWide.Proof.ofFinishE z)) ∧
    (∀ x s, ∃ z, (AspisR1CurrentWide.Proof.finishConcreteField ops).mulM31 x s = ok z) ∧
    (∀ x y, CWW (AspisR1CurrentWide.Proof.ofFinishE x) → CWW (AspisR1CurrentWide.Proof.ofFinishE y) →
      ∃ z, (AspisR1CurrentWide.Proof.finishCheckedArithmetic ops).add x y = ok z ∧
        CWW (AspisR1CurrentWide.Proof.ofFinishE z)) ∧
    (∀ x s, ∃ z, (AspisR1CurrentWide.Proof.finishCheckedArithmetic ops).mulM31 x s = ok z) ∧
    (∀ x y, CWW (AspisR1CurrentWide.Proof.ofFinishE x) → CWW (AspisR1CurrentWide.Proof.ofFinishE y) →
      ∃ z, (AspisR1CurrentWide.Proof.finishArithmetic ops).add x y = ok z ∧
        CWW (AspisR1CurrentWide.Proof.ofFinishE z)) ∧
    (∀ x s, ∃ z, (AspisR1CurrentWide.Proof.finishArithmetic ops).mulM31 x s = ok z) :=
  ⟨finishAdd_W, finishScale_ok, finishAdd_W, finishScale_ok, finishAdd_W, finishScale_ok⟩

theorem NHE_ops_W :
    (∀ x y, CWW (AspisR1CurrentWide.Proof.ofFinishE x) → CWW (AspisR1CurrentWide.Proof.ofFinishE y) →
      ∃ z, NHE_DotBody.ops.add x y = ok z ∧ CWW (AspisR1CurrentWide.Proof.ofFinishE z)) ∧
    (∀ x s, ∃ z, NHE_DotBody.ops.mulM31 x s = ok z) :=
  ⟨finishAdd_W, finishScale_ok⟩

/-! ### tx2 query loop on Dcon -/

inductive Reach (proof : Slice U8) (p : verifier.Prepared) (g : Array SAQ_WideABI.E 29#usize)
    (geo : verifier.QueryGeometry) (a0 : verifier.Accumulator) (b0 : verifier.BatchedWeights) :
    verifier.Accumulator → verifier.BatchedWeights → Prop where
  | init : Reach proof p g geo a0 b0 a0 b0
  | step {a b a' b'} : Reach proof p g geo a0 b0 a b → a.next.val < 22 →
      Port3_NativeQueryBody.verifier.candidate.query_values Dcon proof p a g none geo b =
        ok (.Ok (a', b')) → Reach proof p g geo a0 b0 a' b'

theorem reach_domain {proof : Slice U8} {p : verifier.Prepared} {g : Array SAQ_WideABI.E 29#usize}
    {geo : verifier.QueryGeometry} {a0 : verifier.Accumulator} {b0 : verifier.BatchedWeights}
    (d0 : AspisR1.NFS_QueryInvariant.Domain p 10 22 a0 b0)
    {a : verifier.Accumulator} {b : verifier.BatchedWeights}
    (reach : Reach proof p g geo a0 b0 a b) : AspisR1.NFS_QueryInvariant.Domain p 10 22 a b := by
  induction reach with
  | init => exact d0
  | step _ inside run ih =>
    exact AspisR1.NFS_QueryInvariant.step NJJ_QueryOps.concrete proof p g geo 10 22 _ _ _ _ ih
      (by decide) inside run

theorem Dcon_values_canon (q : Slice U8) (values : Array SAQ_WideABI.E 4#usize)
    (run : Dcon.op0 4#usize
      (Port3_NativeQueryBody.verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact Dcon) q = ok values) :
    ∀ x ∈ values.val, Port4C_QueryArithmetic.CanonE x := by
  apply AspisR1.NFS_CallerDomains.array_property _ _ q values Port4C_QueryArithmetic.CanonE ?_ run
  intro state i value next call
  unfold Port3_NativeQueryBody.verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut at call
  obtain ⟨bytes, _, call⟩ := Port3_PushFrame.bind_success _ _ _ call
  obtain ⟨decoded, hdecoded, call⟩ := Port3_PushFrame.bind_success _ _ _ call
  cases Result.ok.inj call
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := SAQ_Decoder_read_lt _ _ _ hdecoded
  exact ⟨⟨h0, h1, h2, h3⟩, ⟨h4, h5, h6, h7⟩⟩

/-- Every tx2 query step at every reached state: the CW calls of the circle and line
queries and the accumulate tail calls are ok. Inputs: the tx2 resume success, its
start guard a0.next = 10, and the powers call on the resumed gamma. -/
theorem tx2_step_sites (reservation : NP6_StdModel.Reservation) {H : Type}
    (dg : VTop_Stages.aspis_core.digest.Digest32 H) (ck proof pub : Slice U8) (hash : H)
    (p : verifier.Prepared) (a0 : verifier.Accumulator)
    (entered : NJJ_Common.resume reservation dg ck proof pub .S2 hash = ok (.Ok (p,a0)))
    (start : a0.next.val = 10)
    (gN : Array NFN_LPi_FieldValues.NE 29#usize)
    (powers : FIo_Native.weights.powers 29#usize (FIo_Install.toE p.gamma) = ok gN)
    (geo : verifier.QueryGeometry) {a : verifier.Accumulator} {b : verifier.BatchedWeights}
    (reach : Reach proof p (FIp_DotsAdapter.fromArray gN) geo a0 (AspisR1.NFW_QueryResume.pending a0) a b)
    (q : Slice U8) (values : Array SAQ_WideABI.E 4#usize)
    (runValues : Dcon.op0 4#usize
      (Port3_NativeQueryBody.verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact Dcon) q = ok values)
    (dots : Array SAQ_WideABI.E 4#usize) (qPlace gPlace : Nat)
    (runDots : FIp_DotsAdapter.dots q (FIp_DotsAdapter.fromArray gN) = ok dots)
    (we4 we6 : SAQ_WideABI.E) (h0 : Array.index_usize p.alpha 0#usize = ok we4)
    (h1 : Array.index_usize p.alpha 1#usize = ok we6) (inverse : Array U32 5#usize) :
    (∃ folded, Dcon.op17 we4 dots inverse = ok folded ∧ Port4C_QueryArithmetic.CanonE folded) ∧
    ∃ folded1, Dcon.op16 we6 values inverse = ok folded1 ∧
      ∃ we we1 q', Dcon.op3 folded1 a.power = ok we ∧ NBO_TailDomain.WideCanonical we ∧
        Dcon.op2 a.rhs we = ok we1 ∧ NBO_TailDomain.WideCanonical we1 ∧
        Dcon.op9 a.power p.rho = ok q' ∧ NBF_PowerStep.Canonical q' := by
  obtain ⟨d, same, size⟩ := entered_domain reservation dg ck proof pub hash p a0 entered
  obtain ⟨inv0, gamma⟩ := NID_ResumeQuery.domain _ _ ck proof pub hash p a0 size same start
  have inv := reach_domain inv0 reach
  have gC := AspisR1.NFW_PowersDomain.query_domain _ gamma gN powers
  have cd := AspisR1.NFS_CallerDomains.dots q (FIp_DotsAdapter.fromArray gN) qPlace gPlace gC dots runDots
  have cv := Dcon_values_canon q values runValues
  refine ⟨circle_site we4 dots inverse (resume_alpha_canonE d 0#usize (by decide) we4 h0) cd, ?_⟩
  obtain ⟨folded1, hl, _⟩ := line_site we6 values inverse (resume_alpha_canonE d 1#usize (by decide) we6 h1) cv
  have wc := AspisR1.NFS_AccumDomain.line we6 values inverse folded1 hl
  exact ⟨folded1, hl, tail_sites inv folded1 wc⟩

#print axioms ecanon_W
#print axioms ecanon_canonE
#print axioms entered_domain
#print axioms alpha_read
#print axioms resume_alpha_W
#print axioms resume_alpha_canonE
#print axioms tx2_finish_body
#print axioms tx2_finish_round
#print axioms tx2_finish_round_entered
#print axioms finishOps_round_slots
#print axioms finishOps_round_sites
#print axioms kernel_slots
#print axioms finishScale_ok
#print axioms finishConcreteField_slots
#print axioms finishConcreteField_W
#print axioms NHE_ops_W
#print axioms reach_domain
#print axioms Dcon_values_canon
#print axioms tx2_step_sites
end AspisR1.NPH_R22JoinCW2
