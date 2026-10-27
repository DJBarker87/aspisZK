import FJq_ClaimZero
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJq_MaskC1Value
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open FIp_SemanticValues (decode)
open FIz_ConcretePack (embed)
theorem value {H : Type} (D : aspis_core.Digest32 H) (c : FJn_MaskC1Gather.Claims)
    (out : Array aspis_core.field.QM31 16#usize)
    (run : OraclePortStdBuilder.fromFn 16#usize (FinishModel.closureFn9 D) c=ok out) :
    FJn_MaskWide.cell16 out=fun i=>embed (FJn_MainClaims.claims c 0 ⟨i.val,by omega⟩) := by
  have ordered:=FIw_BuilderValue.fromFn 16#usize (FinishModel.closureFn9 D) decode
    (fun c i=>FJq_MaskC1Callback.lookup c i.val) (FJq_MaskC1Callback.selected D) c out run
  have cells:=FJq_MainIndices.value out (fun i=>FJq_MaskC1Callback.lookup c i) ordered
  funext i
  have same:=cells i
  rw [FJq_ClaimZero.value c ⟨i.val,by omega⟩] at same
  exact congrArg embed same
#print axioms value
end AspisR1.FJq_MaskC1Value
end
