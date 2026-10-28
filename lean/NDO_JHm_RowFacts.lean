import NDO_JHm_Arithmetic
import NDO_JFu_ClaimsData
import CurrentClaimSourceAggregation
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHm_RowFacts
open Aeneas Aeneas.Std
open AspisR1ClaimPreparedBridge
abbrev scalar (q : AspisR1PublicPreparation.aspis_core.field.QM31) :=
  AspisR1S5ClaimScalarEmbeddedProductSum.scalarEmbed (toClaimQ q)
theorem length (p : Fin 6) : (JHm_Arithmetic.row p.val).length=29 := by
  fin_cases p <;> rfl
#print axioms length

theorem row0 : JFu_ClaimsData.a0.val.map scalar=JHm_Arithmetic.row 0 := rfl
#print axioms row0
theorem row1 : JFu_ClaimsData.a1.val.map scalar=JHm_Arithmetic.row 1 := rfl
#print axioms row1
theorem row2 : JFu_ClaimsData.a2.val.map scalar=JHm_Arithmetic.row 2 := rfl
#print axioms row2
theorem row3 : JFu_ClaimsData.a3.val.map scalar=JHm_Arithmetic.row 3 := rfl
#print axioms row3
end AspisR1.JHm_RowFacts
end
