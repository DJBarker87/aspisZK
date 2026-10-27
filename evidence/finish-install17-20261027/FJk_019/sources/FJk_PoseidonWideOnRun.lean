import FJk_FamilyWide
import FJk_PoseidonPackedAt
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJk_PoseidonWideOnRun
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeValue (K decode)
open FIw_ArrayValue (canonical decoded)
open FIw_PublicModel (Selectors Openings Public)
open FIz_ConcretePack (embed)
attribute [local irreducible] R0P.poseidonScalarResidual
  FIw_PublicModel.openings FIw_PublicModel.selector
/-- Complete Native07 value as the existing Wide packed family on SAME operands. -/
theorem value (pub : Public) (o : Openings) (point : Array field.QM31 10#usize)
    (s : Selectors) (po : state_only_poseidon.StateOnlyPoseidonSelectors)
    (out : Array field.QM31 4#usize)
    (hz : canonical o.z) (ht : canonical o.succ_z) (hx : canonical o.xor12_z)
    (hp : canonical point)
    (boxed : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point=ok s)
    (selectors : pool_v1.pair_forest_semantic_terminal.poseidon_selectors s=ok po)
    (run : state_only_poseidon.evaluate_state_only_poseidon_oracle_projected o po=ok out) :
    canonical out ∧ (fun g=>embed (decoded out g))=fun g : Fin 4=>
      ((R0P.poseidonPackedFamily ConcretePackBasis.basis).residuals
        (SpendDataMap.mapPublic embed (FIw_PublicModel.ofPublic pub))
        (ValueFamilyFieldTransport.mapOpenings embed (FIw_PublicModel.openings o))
        (fun i=>embed (FIw_PublicModel.selector s i))).getD g.val 0 := by
  have ca := FJa_BoxedCanonical.value point s hp boxed
  have ps := FJa_PoseidonSelectors.value s po ca.1 ca.2 selectors
  have v := FJk_Native07Value.value o po out hz ht hx ps.2.1 ps.2.2.1 run
  refine ⟨v.1,?_⟩
  funext g
  rw [v.2,FJh_WidePack.value,FJk_PoseidonPackedAt.value]
  apply congrArg (R0P.pack4 ConcretePackBasis.basis)
  funext j
  exact FJk_FamilyWide.scalar point s po o hp boxed selectors (FJe_ExternalAdjoint.lane g j)
#print axioms value
end AspisR1.FJk_PoseidonWideOnRun
end
