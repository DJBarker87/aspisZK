import FJn_MainArrayValue
import FIw_BuilderValue
import FIr_BuilderCanonical
import FIr_AcceptedTerminal
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJn_MaskC1Gather
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open FIp_SemanticValues (Canon decode)
abbrev Claims:=Array (Array aspis_core.field.QM31 29#usize) 3#usize
def CanonClaims (c : Claims) : Prop:=∀ row∈c.val,∀ x∈row.val,Canon x
/-- Complete actual first16-cell source mask gather, retaining SAME row0. -/
theorem canonical {H : Type} (D : aspis_core.Digest32 H) (claims : Claims)
    (out : Array aspis_core.field.QM31 16#usize) (hc : CanonClaims claims)
    (run : OraclePortStdBuilder.fromFn 16#usize (FinishModel.closureFn9 D) claims=ok out) :
    ∀ x∈out.val,Canon x := by
  apply FIr_BuilderCanonical.fromFn 16#usize (FinishModel.closureFn9 D) CanonClaims Canon _ claims out hc run
  intro c i x c' all called
  unfold FinishModel.closureFn9 FinishModel.closureFn6 at called
  obtain ⟨row,rr,called⟩:=FIv_Map.bind_success _ _ _ called
  obtain ⟨q,rq,called⟩:=FIv_Map.bind_success _ _ _ called
  obtain ⟨rfl,rfl⟩:=Prod.mk.inj (Result.ok.inj called)
  exact ⟨all row (FIr_ArrayRead.member c 0#usize row rr) q (FIr_ArrayRead.member row i q rq),all⟩
#print axioms canonical
end AspisR1.FJn_MaskC1Gather
end
