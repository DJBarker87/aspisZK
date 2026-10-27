import RPv_FJq_MaskOnlyCallback
import RPv_FJq_ClaimZero
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJq_MaskOnlyValue
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open FIp_SemanticValues (decode)
open FIz_ConcretePack (embed)
theorem value {H : Type} (D : aspis_core.Digest32 H) (c : FJn_MaskC1Gather.Claims)
    (out : Array aspis_core.field.QM31 10#usize)
    (run : OraclePortStdBuilder.fromFn 10#usize (FinishModel.closureFn5 D) c=ok out) :
    FJn_MaskWide.cell10 out=fun i=>embed (FJn_MainClaims.claims c 0 ⟨16+i.val,by omega⟩) := by
  have ordered:=FIw_BuilderValue.fromFn 10#usize (FinishModel.closureFn5 D) decode
    (fun c i=>FJq_MaskC1Callback.lookup c (16+i.val)) (FJq_MaskOnlyCallback.selected D) c out run
  have cells:=FJq_MainIndices.value out (fun i=>FJq_MaskC1Callback.lookup c (16+i)) ordered
  funext i
  have same:=cells i
  rw [FJq_ClaimZero.value c ⟨16+i.val,by omega⟩] at same
  exact congrArg embed same
#print axioms value
end AspisR1.FJq_MaskOnlyValue
end
