import FJk_OpeningsModel
import FJk_PackedWide
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJk_PoseidonFamily
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeValue (K decode)
open FIw_ArrayValue (canonical decoded)
open FIw_PublicModel (Selectors Openings Public)
attribute [local irreducible] R0P.poseidonScalarResidual
/-- The exact scalar-family parameters come from the SAME boxed point. -/
theorem scalar (point : Array field.QM31 10#usize) (s : Selectors)
    (po : state_only_poseidon.StateOnlyPoseidonSelectors) (o : Openings)
    (hp : canonical point)
    (boxed : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point=ok s)
    (run : pool_v1.pair_forest_semantic_terminal.poseidon_selectors s=ok po) (lane : Fin 16) :
    R0P.poseidonScalarResidual (FJh_Native07RawValue.openings o) (decode po.block)
      (decoded po.local) lane =
    R0P.poseidonScalarResidual (FIw_PublicModel.openings o)
      (R0P.g2SumHigh (FIw_PublicModel.selector s) 0 57 (by decide))
      (R0P.g2Low (FIw_PublicModel.selector s)) lane := by
  have h := FJk_SelectorModel.value point s po hp boxed run
  rw [FJk_OpeningsModel.value,h.2.1,h.2.2]
#print axioms scalar
end AspisR1.FJk_PoseidonFamily
end
