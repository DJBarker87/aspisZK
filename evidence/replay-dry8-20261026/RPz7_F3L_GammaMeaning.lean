import RPz7_CurrentPreparedGammaRank
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3L_GammaMeaning
open Aeneas Aeneas.Std Result
open AspisR1CurrentPreparedClaim.Concrete AspisR1ClaimPreparedBridge
open AspisV8R19.SqueezeOracleBridge

theorem value (block : Array U8 32#usize) (out : PE)
    (success : candidateGammaPublic block=ok out) :
    decode (toClaimE out)=R0C.ModuloField.gamma (decodeState block) := by
  obtain ⟨r,rank,decoded⟩ := candidateGammaPublic_success_rank block out success
  rw [decoded]
  apply congrArg R0C.ModuloField.fieldRank
  apply Fin.ext
  exact rank

#print axioms value
end AspisR1.F3L_GammaMeaning
end
