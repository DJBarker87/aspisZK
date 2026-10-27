import RPv_FJa_ClaimsReference
import RPv_FIr_CarrierCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJa_ClaimsCanonical
open Aeneas Aeneas.Std Result
open ClaimsUnrolledFinish
/-- Actual reference success derives all3×29 canonical claim cells, including
unused column28; it does not assume the desired output's canonicality. -/
theorem value (std : StdCalls) (pre : MainPrefix) (out : MainClaims)
    (run : reference std pre=ok (.Ok out)) :
    ∀ row∈out.val,∀ q∈row.val,FIp_SemanticValues.Canon q := by
  unfold reference at run
  cases hp : AspisR1ClaimsUnrolledParent.claimsReference (external std) (fromMainPrefix pre) with
  | fail e => rw [hp] at run;cases run
  | div => rw [hp] at run;cases run
  | ok status =>
    rw [hp] at run
    cases status with
    | Err e => cases run
    | Ok claims =>
      have same : (⟨claims.val.map toMainArray,by simpa using claims.property⟩ : MainClaims)=out :=
        core.result.Result.Ok.inj (Result.ok.inj run)
      subst out
      obtain ⟨record,decoded⟩ := FJa_ClaimsReference.reached _ _ claims hp
      have hc := FJa_ClaimsRows.value std record claims decoded
      intro row member q hq
      obtain ⟨sourceRow,sourceMem,rfl⟩ := List.mem_map.mp member
      obtain ⟨sourceQ,sourceQMem,rfl⟩ := List.mem_map.mp hq
      exact hc sourceRow sourceMem sourceQ sourceQMem
#print axioms value
end AspisR1.FJa_ClaimsCanonical
end
