import FJq_MaskC1Callback
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJq_MaskOnlyCallback
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open FIp_SemanticValues (decode)
theorem selected {H : Type} (D : aspis_core.Digest32 H) (c : FJn_MaskC1Gather.Claims)
    (i : Usize) (x : aspis_core.field.QM31) (after : FJn_MaskC1Gather.Claims)
    (run : (FinishModel.closureFn5 D).call_mut c i=ok (x,after)) :
    decode x=FJq_MaskC1Callback.lookup c (16+i.val) ∧ after=c := by
  unfold FinishModel.closureFn5 FinishModel.closureFn2 at run
  obtain ⟨index,ri,run⟩:=FIv_Map.bind_success _ _ _ run
  obtain ⟨row,rr,run⟩:=FIv_Map.bind_success _ _ _ run
  obtain ⟨q,rq,run⟩:=FIv_Map.bind_success _ _ _ run
  obtain ⟨rfl,rfl⟩:=Prod.mk.inj (Result.ok.inj run)
  have equation:=UScalar.add_equiv (16#usize) i
  rw [ri] at equation
  have add : index.val=16+i.val := equation.2.1
  have rowValue : c.val[0]?=some row := by simpa using FIr_ArrayRead.slot c 0#usize row rr
  simp only [FJq_MaskC1Callback.lookup,rowValue]
  rw [←add]
  exact ⟨(FJn_MainArrayValue.read row index q rq).symm,True.intro⟩
#print axioms selected
end AspisR1.FJq_MaskOnlyCallback
end
