import NHC_DecodeReject
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace NHC_DecodeAccepted
/-- All successful model cuts use THAT body and THAT decoded record. The decoder
and account domains are conclusions; there is no bundled output-equality input. -/
theorem domains (input : Slice U8) (count : Nat) (request : NHC_DecodeModel.Request)
    (hints : NHC_DecodeModel.Hints)
    (accepted : NHC_DecodeModel.run input count = ok (.Ok (request,hints))) :
    ∃ body : Slice U8,
      NHC_Hints.pair_forest.split_pair_forest_terminal_bump_hints_v1 input = ok (.Ok (body,hints)) ∧
      AspisR1.NFY_JHd_RequestNative.decode body = ok (.Ok request) ∧
      input.val.length = 324 ∧ body.val.length = 320 ∧ 3 ≤ count := by
  have width : input.val.length = 324 := by
    by_contra bad
    have rejected := NHC_DecodeReject.wrong_length input count bad
    rw [accepted] at rejected
    cases rejected
  obtain ⟨body,hints',strip,_,_⟩ := NHC_HintsTotal.split input (by omega)
  rw [NHC_DecodeModel.run,strip] at accepted
  simp only [bind_tc_ok] at accepted
  cases hd : AspisR1.NFY_JHd_RequestNative.decode body with
  | ok decoded =>
    rw [hd] at accepted
    simp only [bind_tc_ok] at accepted
    cases decoded with
    | Err e => simp [NHC_DecodeModel.afterDecode] at accepted
    | Ok r =>
      by_cases few : count < 3
      · simp [NHC_DecodeModel.afterDecode,few] at accepted
      · have same : (r,hints') = (request,hints) :=
          by simpa [NHC_DecodeModel.afterDecode,few] using accepted
        have req : r=request := congrArg Prod.fst same
        have hs : hints'=hints := congrArg Prod.snd same
        subst r
        subst hints'
        exact ⟨body,strip,hd,width,NHC_NGG_RequestLength.decoder body request hd,by omega⟩
  | fail e => simp [hd] at accepted
  | div => simp [hd] at accepted
#print axioms domains
end NHC_DecodeAccepted
