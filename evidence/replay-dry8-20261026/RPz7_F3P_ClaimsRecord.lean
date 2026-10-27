import RPz7_F3P_ClaimsMain
set_option autoImplicit false
namespace AspisR1.F3P_ClaimsRecord
open Aeneas Aeneas.Std Result ClaimsUnrolledFinish

theorem source (pre : MainPrefix) (r : AspisR1ClaimsUnrolledParent.r1_wire.ValidatedRecord)
    (success : sourceRecord (fromMainPrefix pre) 25#u8=ok (.Ok r)) :
    AspisR1PublicPreparation.r1_wire.Prefix.validated_record pre 25#u8=ok (.Ok (toMainRecord r)) := by
  unfold sourceRecord at success
  have round : toMainPrefix (fromMainPrefix pre)=pre := by cases pre;rfl
  rw [round] at success
  cases h : AspisR1PublicPreparation.r1_wire.Prefix.validated_record pre 25#u8 with
  | fail e => simp only [h] at success;cases success
  | div => simp only [h] at success;cases success
  | ok result =>
    cases result with
    | Err e => simp only [h] at success;cases success
    | Ok a =>
      simp only [h] at success
      have same := core.result.Result.Ok.inj (Result.ok.inj success)
      rw [← same]
      cases a
      rfl

#print axioms source
end AspisR1.F3P_ClaimsRecord
