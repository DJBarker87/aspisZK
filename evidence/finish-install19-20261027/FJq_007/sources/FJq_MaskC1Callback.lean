import FJq_MainIndices
import FJn_MaskC1Gather
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJq_MaskC1Callback
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open FIp_SemanticValues (decode)
abbrev Claims:=FJn_MaskC1Gather.Claims
def at (c : Claims) (i : Nat) : FIv_NativeValue.K :=
  match c.val[0]? with | none=>0 | some row=>FJn_MainArrayValue.value row i
theorem selected {H : Type} (D : aspis_core.Digest32 H) (c : Claims)
    (i : Usize) (x : aspis_core.field.QM31) (after : Claims)
    (run : (FinishModel.closureFn9 D).call_mut c i=ok (x,after)) :
    decode x=at c i.val ∧ after=c := by
  unfold FinishModel.closureFn9 FinishModel.closureFn6 at run
  obtain ⟨row,rr,run⟩:=FIv_Map.bind_success _ _ _ run
  obtain ⟨q,rq,run⟩:=FIv_Map.bind_success _ _ _ run
  obtain ⟨rfl,rfl⟩:=Prod.mk.inj (Result.ok.inj run)
  simp only [at,FIr_ArrayRead.slot c 0#usize row rr]
  exact ⟨(FJn_MainArrayValue.read row i q rq).symm,rfl⟩
#print axioms selected
end AspisR1.FJq_MaskC1Callback
end
