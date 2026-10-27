import RPu_FIv_Arithmetic
import RPz7_ClaimsUnrolledFinish
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJq_SourceDecode
open Aeneas Aeneas.Std Result ClaimsUnrolledFinish
/-- Nominal parent adapter does not choose a different decode result. -/
theorem reached (n : Usize) (record : AspisR1ClaimsUnrolledParent.Record)
    (offset : Usize) (out : Array ParentQM n)
    (run : sourceDecode n record offset=ok (.Ok out)) :
    ∃ a : Array MainQM n,
      AspisS1ExtractedRoundChildren.decodeMain n (toMainRecord record) offset=ok (.Ok a) ∧
      out=fromMainArray a := by
  unfold sourceDecode at run
  cases called : AspisS1ExtractedRoundChildren.decodeMain n (toMainRecord record) offset with
  | fail e=>rw [called] at run;cases run
  | div=>rw [called] at run;cases run
  | ok status=>
    rw [called] at run
    cases status with
    | Err e=>cases run
    | Ok a=>exact ⟨a,rfl,(core.result.Result.Ok.inj (Result.ok.inj run)).symm⟩
#print axioms reached
end AspisR1.FJq_SourceDecode
end
