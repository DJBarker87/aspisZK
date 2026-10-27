import FJn_MaskC1Gather
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJn_MaskOnlyGather
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open FIp_SemanticValues (Canon)
/-- Complete actual10-cell source mask-only gather, retaining source row0. -/
theorem canonical {H : Type} (D : aspis_core.Digest32 H) (claims : FJn_MaskC1Gather.Claims)
    (out : Array aspis_core.field.QM31 10#usize) (hc : FJn_MaskC1Gather.CanonClaims claims)
    (run : OraclePortStdBuilder.fromFn 10#usize (FinishModel.closureFn5 D) claims=ok out) :
    ∀ x∈out.val,Canon x := by
  apply FIr_BuilderCanonical.fromFn 10#usize (FinishModel.closureFn5 D) FJn_MaskC1Gather.CanonClaims Canon _ claims out hc run
  intro c i x c' all called
  unfold FinishModel.closureFn5 FinishModel.closureFn2 at called
  obtain ⟨index,ri,called⟩:=FIv_Map.bind_success _ _ _ called
  obtain ⟨row,rr,called⟩:=FIv_Map.bind_success _ _ _ called
  obtain ⟨q,rq,called⟩:=FIv_Map.bind_success _ _ _ called
  obtain ⟨rfl,rfl⟩:=Prod.mk.inj (Result.ok.inj called)
  exact ⟨all row (FIr_ArrayRead.member c 0#usize row rr) q (FIr_ArrayRead.member row index q rq),all⟩
#print axioms canonical
end AspisR1.FJn_MaskOnlyGather
end
