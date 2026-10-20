import CurrentFinishEquality
import FinishFieldSelectorAdapterV2
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentWide.Proof

def finishField (bytes : Slice U8) (i : Usize) : Result FinishE := do
  let value ← AspisR1WeightsFieldCurrent.weights.field
    AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes bytes i
  ok (recordWideToFinish value)

theorem finishField_success_canonical (bytes : Slice U8) (i : Usize) (value : FinishE)
    (h : finishField bytes i = .ok value) : CanonicalFinish value := by
  unfold finishField at h
  cases hs : AspisR1WeightsFieldCurrent.weights.field
      AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes bytes i with
  | fail e => simp only [hs,bind_tc_fail] at h; cases h
  | div => simp only [hs,bind_tc_div] at h; cases h
  | ok out =>
    simp only [hs,bind_tc_ok] at h
    have he : recordWideToFinish out=value := Result.ok.inj h
    rw [←he]
    exact record_field_finish_canonical bytes i out hs

def finishConcreteField {W D : Type} (ops : AspisR1FinishRelationCurrent.FinishOps W D) :
    AspisR1FinishRelationCurrent.FinishOps W D :=
  finishCheckedArithmetic {ops with field:=finishField}

theorem concrete_finish_round_success {W D : Type}
    (ops : AspisR1FinishRelationCurrent.FinishOps W D)
    (poly : Slice U8) (alpha claim out : FinishE) (round : Usize)
    (hc : CanonicalFinish claim)
    (h : AspisR1FinishRelationCurrent.verifier.finish_relation_round
      (finishConcreteField ops) poly alpha claim round = .ok (.Ok out)) :
    (∃ x0 x4, finishField poly 0#usize=.ok x0 ∧ finishField poly 4#usize=.ok x4 ∧
      decodeFinish x0+decodeFinish x4=decodeFinish claim * (536870912 : AspisWideTower.WideExact)) ∧
      ops.polynomial poly alpha = .ok out := by
  constructor
  · exact current_checked_round_equation {ops with field:=finishField} poly alpha claim out round
      hc (finishField_success_canonical poly 0#usize) (finishField_success_canonical poly 4#usize) h
  · have hr := AspisR1FinishRelationCurrent.FinishCandidateEquations.round_equation
      (finishConcreteField ops) finish_eq_success_true poly alpha claim out round h
    rcases hr with ⟨_,_,_,_,_,_,_,_,_,_,_,hp⟩
    exact hp

#print axioms finishField_success_canonical
#print axioms concrete_finish_round_success
end AspisR1CurrentWide.Proof
