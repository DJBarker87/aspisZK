import F3N_OriginalClaim
import F3L_RhoMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3N_SelectedScalar
open AspisR1ClaimPreparedBridge

theorem numeric (q : AspisR1CurrentPreparedClaim.aspis_core.field.QM31) :
    AspisR1S5ClaimScalarEmbeddedProductSum.scalarEmbed q=
      LiteralOpeningView.eK (F3L_RhoMeaning.decode (fromClaimQ q)) := by
  rfl

#print axioms numeric
end AspisR1.F3N_SelectedScalar
end
