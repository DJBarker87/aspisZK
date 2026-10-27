import RPv_FJk_Native07Value
import RPv_FIz_RangeMarginal
import RPv_FJa_BoxedMass
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJk_SelectorModel
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeValue (K decode)
open FIw_ArrayValue (canonical decoded)
open FIw_PublicModel (Selectors)
/-- Same installed selector constructor, with its marginal masses derived. -/
theorem value (point : Array field.QM31 10#usize) (s : Selectors)
    (out : state_only_poseidon.StateOnlyPoseidonSelectors)
    (hp : canonical point)
    (boxed : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point=ok s)
    (run : pool_v1.pair_forest_semantic_terminal.poseidon_selectors s=ok out) :
    out.local=s.low ∧
    decoded out.local=R0P.g2Low (FIw_PublicModel.selector s) ∧
    decode out.block=R0P.g2SumHigh (FIw_PublicModel.selector s) 0 57 (by decide) := by
  have ca := FJa_BoxedCanonical.value point s hp boxed
  have ma := FJa_BoxedMass.value point s hp boxed
  have po := FJa_PoseidonSelectors.value s out ca.1 ca.2 run
  refine ⟨po.1,?_,?_⟩
  · rw [po.1]
    funext l
    rw [FIz_Marginals.low s ma.1 l]
    exact (FJh_LowModels.cell s.low l.val l.isLt).symm
  · exact po.2.2.2.trans (FIz_RangeMarginal.value s ma.2 0 57 (by decide))
#print axioms value
end AspisR1.FJk_SelectorModel
end
