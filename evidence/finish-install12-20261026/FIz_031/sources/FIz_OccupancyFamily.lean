import FIy_OccupancyModel
import FIy_OccupancyPacked
import FIw_PublicModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIz_OccupancyFamily
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
  change R0P.occupancyLanesLiteral _ _ _ _=R0P.occupancyLanesLiteral _ _ _ _
  apply congrArg (fun (args : K × K × K × (Fin 16 → K)) => R0P.occupancyLanesLiteral args.1 args.2.1 args.2.2.1 args.2.2.2)
  rfl
#print axioms value
end AspisR1.FIz_OccupancyFamily
end
