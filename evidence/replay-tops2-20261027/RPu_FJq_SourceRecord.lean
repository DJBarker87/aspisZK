import RPz7_ClaimsUnrolledFinish
import RPu_FIv_Arithmetic
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJq_SourceRecord
open Aeneas Aeneas.Std Result ClaimsUnrolledFinish
/-- The normalized record is the SAME prefix getter result, including framing. -/
theorem reached (pre : AspisR1ClaimsUnrolledParent.r1_wire.Prefix) (row : U8)
    (record : AspisR1ClaimsUnrolledParent.Record)
    (run : sourceRecord pre row=ok (.Ok record)) :
    AspisR1PublicPreparation.r1_wire.Prefix.validated_record (toMainPrefix pre) row=
      ok (.Ok (toMainRecord record)) := by
  unfold sourceRecord at run
  cases called : AspisR1PublicPreparation.r1_wire.Prefix.validated_record (toMainPrefix pre) row with
  | fail e=>rw [called] at run;cases run
  | div=>rw [called] at run;cases run
  | ok status=>
    rw [called] at run
    cases status with
    | Err e=>cases run
    | Ok r=>
      have same:=core.result.Result.Ok.inj (Result.ok.inj run)
      cases same
      rfl
#print axioms reached
end AspisR1.FJq_SourceRecord
end
