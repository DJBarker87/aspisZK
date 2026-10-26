import RPz7_F3P_GammaCell
import RPz7_F3N_SelectedScalar
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3P_LowProjection
open AspisR1CurrentPreparedClaim.Concrete AspisR1ClaimPreparedBridge

theorem lower (value : E) :
    LiteralOpeningView.eK (F3L_RhoMeaning.decode (fromClaimQ value.c0))=
      (⟨(decode value).re,0⟩ : AspisWideTower.WideExact) := by
  apply QuadraticAlgebra.ext
  · rfl
  · rfl

#print axioms lower
end AspisR1.F3P_LowProjection
end
