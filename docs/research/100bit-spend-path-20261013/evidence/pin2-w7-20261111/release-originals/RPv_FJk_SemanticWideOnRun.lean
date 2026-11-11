import RPv_FJk_ScalarLaneMap
import RPv_FIz_WideCoefficientsOnRun
import RPv_FJa_BoxedMass
import RPv_FJa_PublicBounds
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJk_SemanticWideOnRun
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeValue (K)
open FIw_ArrayValue (canonical decoded)
open FIw_PublicModel (Public Openings Selectors)
open FIz_ConcretePack (embed)
attribute [local irreducible] FIw_PublicModel.ofPublic FIw_PublicModel.openings FIw_PublicModel.selector
/-- All 24 actual semantic outputs interpreted in Wide on SAME public/point/openings. -/
theorem value (p : Public) (o : Openings) (s : Selectors) (point : Array field.QM31 10#usize)
    (out : Array field.QM31 24#usize)
    (hz : canonical o.z) (hs : canonical o.succ_z) (hx : canonical o.xor12_z)
    (hp : canonical point) (bounds : FJa_PublicBounds.Bounds p)
    (boxed : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point=ok s)
    (run : pool_v1.pair_forest_semantic_terminal.semantic_packed p o s=ok out) :
    canonical out ∧ (fun j=>embed (decoded out j))=fun j=>R0P.pack4 ConcretePackBasis.basis
      (fun i=>R0P.SemSource.scalarLaneAt (SpendDataMap.mapPublic embed (FIw_PublicModel.ofPublic p))
        (ValueFamilyFieldTransport.mapOpenings embed (FIw_PublicModel.openings o))
        (fun k=>embed (FIw_PublicModel.selector s k)) (4*j.val+i.val)) := by
  have cs := FJa_BoxedCanonical.value point s hp boxed
  have ms := FJa_BoxedMass.value point s hp boxed
  obtain ⟨ha,hn,hchange,hr,hf,hnr,hnf,hab,haw⟩ := bounds
  have v := FIz_WideCoefficientsOnRun.on_run p o s out hz hs hx cs.1 cs.2
    ha hn hr hchange hf hnr hnf hab haw ms.1 ms.2 run
  refine ⟨v.1,v.2.trans ?_⟩
  funext j
  apply congrArg (R0P.pack4 ConcretePackBasis.basis)
  funext i
  exact FJk_ScalarLaneMap.value embed (FIw_PublicModel.ofPublic p)
    (FIw_PublicModel.openings o) (FIw_PublicModel.selector s) (4*j.val+i.val)
#print axioms value
end AspisR1.FJk_SemanticWideOnRun
end
