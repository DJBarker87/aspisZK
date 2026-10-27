import RPv_FIy_OccupancyModel
import RPv_FIy_OccupancyPacked
import RPv_FIw_PublicModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIz_OccupancyFamily
attribute [local irreducible] R0P.occupancyLanesLiteral
open FIv_NativeValue (K)
open FIw_PublicModel (Public Openings Selectors)
theorem value (p : Public) (o : Openings) (s : Selectors) :
    List.ofFn (FIy_OccupancyMeaning.model (FIy_OccupancyPacked.input s) (FIy_OccupancyPacked.output s)
      (FIy_OccupancyRows.expected p.variant) (FIv_NativeArray.value o.z)) =
    R0P.occupancyFamily.residuals (FIw_PublicModel.ofPublic p) (FIw_PublicModel.openings o) (FIw_PublicModel.selector s) := by
  rw [FIy_OccupancyModel.value]
  unfold R0P.occupancyFamily
  have expected : (FIy_OccupancyRows.expected p.variant : K)=R0P.occupancyExpected (FIw_CoefficientTransport.variant p.variant) := by
    cases p.variant <;> rfl
  rw [expected]
  simp only [FIy_OccupancyPacked.input,FIy_OccupancyPacked.output,FIw_PublicModel.ofPublic,
    FIw_PublicModel.selector,FIw_PublicModel.openings]
  rfl
#print axioms value
end AspisR1.FIz_OccupancyFamily
end
