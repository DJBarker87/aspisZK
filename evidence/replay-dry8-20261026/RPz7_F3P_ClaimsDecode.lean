import RPz7_F3P_ClaimsMain
set_option autoImplicit false
namespace AspisR1.F3P_ClaimsDecode
open Aeneas Aeneas.Std Result ClaimsUnrolledFinish

theorem arrays (a : Array MainQM 29#usize) : toMainArray (fromMainArray a)=a := by
  apply Subtype.ext
  simp only [toMainArray,fromMainArray,List.map_map,Function.comp_def]
  have qm : ∀ q : MainQM,toMainQM (fromMainQM q)=q := by intro q;cases q; rfl
  simp [qm]

theorem decoded (r : AspisR1ClaimsUnrolledParent.r1_wire.ValidatedRecord) (offset : Usize)
    (out : AspisR1ClaimsUnrolledParent.Row) (success : sourceDecode 29#usize r offset=ok (.Ok out)) :
    AspisS1ExtractedRoundChildren.decodeMain 29#usize (toMainRecord r) offset=ok (.Ok (toMainArray out)) := by
  unfold sourceDecode at success
  cases h : AspisS1ExtractedRoundChildren.decodeMain 29#usize (toMainRecord r) offset with
  | fail e => simp only [h] at success;cases success
  | div => simp only [h] at success;cases success
  | ok result =>
    cases result with
    | Err e => simp only [h] at success;cases success
    | Ok a =>
      simp only [h] at success
      have same := core.result.Result.Ok.inj (Result.ok.inj success)
      rw [← same,arrays]

#print axioms arrays
#print axioms decoded
end AspisR1.F3P_ClaimsDecode
