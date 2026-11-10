import NPR_R22WeightsWidth

set_option autoImplicit false
noncomputable section
namespace AspisR1.NPR_R22DotSite
open Aeneas Aeneas.Std Result AspisR1Stage2

/-- The native finish calls its op4 (the finish dot) only on Vec.deref a.weights. -/
theorem finish_op4_congr {W : Type} (ops : Port3_NativeFinishBody.Ops W)
    (op4' : Slice U8 → Slice aspis_core.field.QM31 →
      Result (core.result.Result aspis_core.field.wide_exact.WideExact verifier.Error))
    (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
    (obs : Option (verifier.Phase → Result Unit))
    (hagree : ∀ fm, op4' fm (alloc.vec.Vec.deref a.weights) = ops.op4 fm (alloc.vec.Vec.deref a.weights)) :
    Port3_NativeFinishBody.verifier.finish_relation { ops with op4 := op4' } v p a obs =
      Port3_NativeFinishBody.verifier.finish_relation ops v p a obs := by
  unfold Port3_NativeFinishBody.verifier.finish_relation
  simp only [hagree]

theorem deref_length {T : Type} (w : alloc.vec.Vec T) :
    (alloc.vec.Vec.deref w).val.length = w.val.length := rfl

theorem mapped_length {A B : Type} (f : A → B) (ws : Slice A) :
    (SAG_DotAdapter.mapSlice f ws).val.length = ws.val.length := by
  simp only [SAG_DotAdapter.mapSlice, List.length_map]

/-- The finish dot loop calls its field slot only at j < len weights. -/
theorem dot_loop_field_congr {W D : Type} (ops : AspisR1FinishRelationCurrent.FinishOps W D)
    (f' : Slice U8 → Usize → Result AspisR1FinishRelationCurrent.aspis_core.field.WideExact) (fm : Slice U8)
    (weights : Slice AspisR1FinishRelationCurrent.aspis_core.field.QM31)
    (hagree : ∀ j, j < Slice.len weights → f' fm j = ops.field fm j) (dot : D) (j : Usize) :
    AspisR1FinishRelationCurrent.verifier.finish_query_dot_loop { ops with field := f' } fm weights dot j =
      AspisR1FinishRelationCurrent.verifier.finish_query_dot_loop ops fm weights dot j := by
  have hb : ∀ (d : D) (i : Usize), AspisR1FinishRelationCurrent.verifier.finish_query_dot_loop.body { ops with field := f' } fm weights d i =
      AspisR1FinishRelationCurrent.verifier.finish_query_dot_loop.body ops fm weights d i := by
    intro d i
    unfold AspisR1FinishRelationCurrent.verifier.finish_query_dot_loop.body
    by_cases hi : i < Slice.len weights
    · simp only [hi, ↓reduceIte, hagree i hi]
    · simp only [hi, ↓reduceIte]
  unfold AspisR1FinishRelationCurrent.verifier.finish_query_dot_loop
  congr 1
  funext x
  obtain ⟨d, i⟩ := x
  exact hb d i

theorem dot_field_congr {W D : Type} (ops : AspisR1FinishRelationCurrent.FinishOps W D)
    (f' : Slice U8 → Usize → Result AspisR1FinishRelationCurrent.aspis_core.field.WideExact) (fm : Slice U8)
    (weights : Slice AspisR1FinishRelationCurrent.aspis_core.field.QM31)
    (hagree : ∀ j, j < Slice.len weights → f' fm j = ops.field fm j) :
    AspisR1FinishRelationCurrent.verifier.finish_query_dot { ops with field := f' } fm weights =
      AspisR1FinishRelationCurrent.verifier.finish_query_dot ops fm weights := by
  unfold AspisR1FinishRelationCurrent.verifier.finish_query_dot
  simp only [dot_loop_field_congr ops f' fm weights hagree]

/-- On weights of length at most 64, the finish dot calls its field slot only at j < 64, where
weights.field's three index operations are ok (NPH_R22FieldSites.domain_ok). -/
theorem dot_guarded {W D : Type} (ops : AspisR1FinishRelationCurrent.FinishOps W D) (fm : Slice U8)
    (weights : Slice AspisR1FinishRelationCurrent.aspis_core.field.QM31) (width : weights.val.length ≤ 64) :
    AspisR1FinishRelationCurrent.verifier.finish_query_dot
        { ops with field := fun fm j => if j.val < 64 then ops.field fm j else fail .panic } fm weights =
      AspisR1FinishRelationCurrent.verifier.finish_query_dot ops fm weights := by
  apply dot_field_congr
  intro j hj
  have hl : (Slice.len weights).val = weights.val.length := by
    rfl
  have hj' : j.val < (Slice.len weights).val := hj
  have small : j.val < 64 := by omega
  simp only [small, ↓reduceIte]

theorem guard_ok3 (j : Usize) (small : j.val < 64) : NPH_R22FieldSites.Ok3 j :=
  NPH_R22FieldSites.domain_ok j small

theorem installed_op4 (r : NP6_StdModel.Reservation) :
    (NIG_Slots.installed r).op4 = (Port3_FinishStage.release (IDa_Deployed.finish r)).dot := rfl

/-- The concrete record of the deployed dot kernel (SAG_DotAdapter.kernel SAG_DotClosed.seed). -/
abbrev R := AspisR1FinishDotConcreteOps.withConcreteDot
  (AspisR1CurrentWide.Proof.finishConcreteField SAG_DotClosed.seed) AspisR1EbyKPushDecodedProductUpdate.QRaw

theorem installed_op4_source (r : NP6_StdModel.Reservation) :
    (NIG_Slots.installed r).op4 = SAG_DotAdapter.sourceDot SAG_DotClosed.seed := rfl

/-- The deployed dot kernel on a slice of length at most 64 equals the same dot whose field slot
runs only at j < 64. -/
theorem kernel_guarded (fm : Slice U8) (ws : Slice AspisR1Stage2.Stage2Finish.K) (width : ws.val.length ≤ 64) :
    SAG_DotAdapter.kernel SAG_DotClosed.seed fm ws =
      AspisR1FinishRelationCurrent.verifier.finish_query_dot
        { R with field := fun fm j => if j.val < 64 then R.field fm j else fail .panic } fm
        (SAG_DotAdapter.mapSlice SAG_DotAdapter.toFinishQ ws) := by
  unfold SAG_DotAdapter.kernel
  exact (dot_guarded R fm _ (by rw [mapped_length]; exact width)).symm

/-- op4 guarded on length 64. -/
def op4G (r : NP6_StdModel.Reservation) : Slice U8 → Slice aspis_core.field.QM31 →
    Result (core.result.Result aspis_core.field.wide_exact.WideExact verifier.Error) := fun fm s =>
  if s.val.length = 64 then (NIG_Slots.installed r).op4 fm s else fail .panic

/-- At an accumulator whose weights have length 64, the deployed finish runs its dot only on a
slice of length 64. -/
theorem deployed_finish_guarded (r : NP6_StdModel.Reservation) (v : verifier.View) (p : verifier.Prepared)
    (a : verifier.Accumulator) (x : Option (VTop_Stages.verifier.Phase → Result Unit)) (h : a.weights.val.length = 64) :
    NLB_Parent.finish r v p a x = NHT_ResultPort.action
      (Port3_NativeFinishBody.verifier.finish_relation { NIG_Slots.installed r with op4 := op4G r } v p a none) := by
  have hag : ∀ fm, op4G r fm (alloc.vec.Vec.deref a.weights) =
      (NIG_Slots.installed r).op4 fm (alloc.vec.Vec.deref a.weights) := by
    intro fm
    unfold op4G
    simp only [deref_length, h, ↓reduceIte]
  unfold NLB_Parent.finish
  exact (congrArg NHT_ResultPort.action (finish_op4_congr (NIG_Slots.installed r) (op4G r) v p a none hag)).symm

/-- Composition, no premise: the deployed tx2 common equals the run whose finish executes only on
accumulators with weights of length 64, and whose finish dot executes only on slices of length 64. -/
theorem deployed_common_dot (env : RSL.Env) (pub proof ck : Slice U8) :
    LIBB_Tx2EnvCode.common env pub proof ck =
      NJJ_Common.run (LIBB_Tx2Reservation.reservation env) (LIBB_Tx2Reservation.reservation env)
        (NLP_NativeMerkle.action (LIBB_PartitionEnv.H env))
        (NPR_R22WeightsWidth.widthGuard (fun v p a _ => NHT_ResultPort.action
          (Port3_NativeFinishBody.verifier.finish_relation
            { NIG_Slots.installed (LIBB_Tx2Reservation.reservation env) with
              op4 := op4G (LIBB_Tx2Reservation.reservation env) } v p a none)))
        (LIBB_PartitionEnv.digest env) pub proof ck () none := by
  rw [NPR_R22WeightsWidth.deployed_common_guarded]
  have e : NPR_R22WeightsWidth.widthGuard (NLB_Parent.finish (LIBB_Tx2Reservation.reservation env)) =
      NPR_R22WeightsWidth.widthGuard (fun v p a _ => NHT_ResultPort.action
          (Port3_NativeFinishBody.verifier.finish_relation
            { NIG_Slots.installed (LIBB_Tx2Reservation.reservation env) with
              op4 := op4G (LIBB_Tx2Reservation.reservation env) } v p a none)) := by
    funext v p a o
    unfold NPR_R22WeightsWidth.widthGuard
    by_cases h : a.weights.val.length = 64
    · simp only [h, ↓reduceIte]
      exact deployed_finish_guarded _ v p a o h
    · simp only [h, ↓reduceIte]
  rw [e]

#print axioms dot_loop_field_congr
#print axioms dot_field_congr
#print axioms dot_guarded
#print axioms guard_ok3
#print axioms installed_op4
#print axioms installed_op4_source
#print axioms kernel_guarded
#print axioms deployed_finish_guarded
#print axioms deployed_common_dot
#print axioms finish_op4_congr
#print axioms deref_length
#print axioms mapped_length
end AspisR1.NPR_R22DotSite
