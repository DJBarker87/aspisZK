import NNV_FinishCut
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_FinishClaims
open Aeneas Aeneas.Std Result AspisR1PublicPreparation LIB_VCarriers

theorem returned (p : Prefix) (env : RSL.Env) (c : Claims)
 (called : LIB_VLib.claimsValue p env = .ok c) :
 env.reservation = true ∧
 ClaimsUnrolledFinish.claims (NP6_StdModel.calls (.Ok ())) (prefixRaw p) = .ok (.Ok (claimsRaw c)) := by
 change (if env.reservation then .ok (LIB_VClaims.value p) else Except.error .Allocation) = .ok c at called
 cases h : env.reservation with
 | false => rw [h] at called; cases called
 | true =>
  rw [h] at called
  have same : LIB_VClaims.value p = c := Except.ok.inj called
  exact ⟨h,same ▸ LIB_VClaims.success_exact p⟩
#print axioms returned
end AspisR1.NNV_FinishClaims
end
