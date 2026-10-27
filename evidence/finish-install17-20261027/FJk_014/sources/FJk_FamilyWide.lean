import FJk_PoseidonFamily
import FJk_ResidualNaturality
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJk_FamilyWide
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeValue (K decode)
open FIw_ArrayValue (canonical decoded)
open FIw_PublicModel (Selectors Openings Public)
open FIz_ConcretePack (embed)
attribute [local irreducible] R0P.poseidonScalarResidual
/-- SAME installed boxed point and openings; no independent family parameters. -/
theorem scalar (point : Array field.QM31 10#usize) (s : Selectors)
    (po : state_only_poseidon.StateOnlyPoseidonSelectors) (o : Openings)
    (hp : canonical point)
    (boxed : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point=ok s)
    (run : pool_v1.pair_forest_semantic_terminal.poseidon_selectors s=ok po) (lane : Fin 16) :
    embed (R0P.poseidonScalarResidual (FJh_Native07RawValue.openings o) (decode po.block)
      (decoded po.local) lane) =
    R0P.poseidonScalarResidual
      (ValueFamilyFieldTransport.mapOpenings embed (FIw_PublicModel.openings o))
      (R0P.g2SumHigh (fun i=>embed (FIw_PublicModel.selector s i)) 0 57 (by decide))
      (R0P.g2Low (fun i=>embed (FIw_PublicModel.selector s i))) lane := by
  exact (congrArg embed (FJk_PoseidonFamily.scalar point s po o hp boxed run lane)).trans
    (FJk_ResidualNaturality.value embed (FIw_PublicModel.openings o)
      (FIw_PublicModel.selector s) lane)
#print axioms scalar
end AspisR1.FJk_FamilyWide
end
