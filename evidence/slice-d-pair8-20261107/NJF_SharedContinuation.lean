import NJF_RegularInstantiation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJF_SharedContinuation
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairControl AspisR1Stage2
open NJF_RegularCut NJF_RegularInstantiation

def continueWith (c : Context) : Result State → Result NR
 | fail err => fail err
 | div => div
 | ok (reply,_,parts) => afterHigh c c.w parts reply

def stage (c : Context) (scratch : Scratch) (parts : Parts) : Result State :=
 match commonReply c with
 | fail err => fail err
 | div => div
 | ok (owner,cells) => match FIo_Native.weights.shared_partials c.f.value cells with
   | fail err => fail err
   | div => div
   | ok (.Err err) => ok (.Err err,scratch,parts)
   | ok (.Ok values) => match FIo_Native.weights.shared_high values owner c.ap0.value c.ap1.value parts with
     | fail err => fail err
     | div => div
     | ok (reply,after) => ok (reply,scratch,after)

/-- The CLOSED common loop gives SAME owner and full cells. This is discharged
internally, so no owner or child-result equation is a root hypothesis. -/
theorem source (c : Context) (scratch : Scratch) (parts : Parts)
 (hf : NHI_TensorOuterStep.Factors c.w.value) :
 continueWith c (stage c scratch parts)=NIT_PairControl.shared c parts := by
 have cz : NHI_CellCanon.array (Array.repeat 16#usize NHX_FilledZero.zeroQ) := by
  intro x hx
  simp only [Array.repeat,List.mem_replicate] at hx
  exact hx.2 ▸ NHX_FilledZero.zero_canonical
 have common := NIW_AlignCommonSource.source c.w.value hf _ cz
 cases hc : commonReply c with
 | fail err =>
  change _ ∧ NIW_AlignFieldReply.Produced (commonReply c) _ at common
  simp only [hc,NIW_AlignFieldReply.Produced] at common
 | div =>
  change _ ∧ NIW_AlignFieldReply.Produced (commonReply c) _ at common
  simp only [hc,NIW_AlignFieldReply.Produced] at common
 | ok value =>
  rcases value with ⟨owner,cells⟩
  change _ ∧ NIW_AlignFieldReply.Produced (commonReply c) _ at common
  have produced := common.2
  simp only [hc,NIW_AlignFieldReply.Produced] at produced
  have same := produced.2.1
  subst owner
  have reference : NIG_CommonLoop.common_reference c.w.value
    (Array.repeat 16#usize NHX_FilledZero.zeroQ)=ok (c.w.value,cells) := by
   rw [←NIG_CommonLoop.common_source]
   exact common.1.trans hc
  cases hp : FIo_Native.weights.shared_partials c.f.value cells with
  | fail err => simp only [stage,hc,hp,continueWith,NIT_PairControl.shared,reference,bind_tc_ok];rfl
  | div => simp only [stage,hc,hp,continueWith,NIT_PairControl.shared,reference,bind_tc_ok];rfl
  | ok partials =>
   cases partials with
   | Err err => simp only [stage,hc,hp,continueWith,NIT_PairControl.shared,reference,bind_tc_ok,afterPartial,afterHigh]
   | Ok values =>
    cases hh : FIo_Native.weights.shared_high values c.w.value c.ap0.value c.ap1.value parts with
    | fail err => simp only [stage,hc,hp,hh,continueWith,NIT_PairControl.shared,reference,bind_tc_ok,afterPartial];rfl
    | div => simp only [stage,hc,hp,hh,continueWith,NIT_PairControl.shared,reference,bind_tc_ok,afterPartial];rfl
    | ok result =>
     rcases result with ⟨reply,after⟩
     simp only [stage,hc,hp,hh,continueWith,NIT_PairControl.shared,reference,bind_tc_ok,afterPartial]

#print source
#print axioms source
end AspisR1.NJF_SharedContinuation
