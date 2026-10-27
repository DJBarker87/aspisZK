import FJn_CopyFullValue
import FJk_SelectorModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJn_CopySelectors
open Aeneas Aeneas.Std Result FIq_Native
open FIw_ArrayValue (canonical)
open FIw_PublicModel (Selectors)
/-- The actual high/low factors are the model marginals, because both masses
are derived from the same boxed constructor. -/
theorem value (point : Array field.QM31 10#usize) (s : Selectors)
    (hp : canonical point)
    (run : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point=ok s) :
    FIw_CopyEndpoint.modelSelectors s=R0P.copySelectors (FIw_PublicModel.selector s) := by
  have mass := FJa_BoxedMass.value point s hp run
  have high : (fun i=>FIv_NativeArray.value s.high i.val)=R0P.g2High (FIw_PublicModel.selector s) :=
    funext (fun i=>(FIz_Marginals.high s mass.2 i).symm)
  have low : (fun i=>FIv_NativeArray.value s.low i.val)=R0P.g2Low (FIw_PublicModel.selector s) :=
    funext (fun i=>(FIz_Marginals.low s mass.1 i).symm)
  unfold FIw_CopyEndpoint.modelSelectors R0P.copySelectors
  rw [high,low]
#print axioms value
end AspisR1.FJn_CopySelectors
end
