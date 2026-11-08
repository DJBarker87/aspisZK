import NMX_R8_Children241
import NMX_R8_Factor241
import NMX_R8_Std241
set_option autoImplicit false
noncomputable section
namespace NMX_R8_AfterFactor241
open Aeneas Aeneas.Std Result AdapterRw NMS_R2N_Interpreted

def source (env : RSL.Env) (choices : NMX_R4_Authentication.Choices)
 (v : r1_pool_adapter.ValidatedAsqa) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) :=
 RSL.Spec.bind (liftResult (Slice.index_usize accounts 0#usize)) fun acc0 =>
 NMS_R2N_RawTry.literal (NMS_R2N_GetterMeaning.meaning acc0) fun proof =>
 RSL.Spec.bind (liftResult (Slice.index_usize accounts 6#usize)) fun acc6 =>
 NMS_R2N_RawTry.literal (NMS_R2N_GetterMeaning.meaning acc6) fun ck =>
 NMX_R8_Factor241.afterReads (NMX_R8_Std241.ops env) (NMX_R8_Children241.grouped choices) v proof ck

theorem factor (env : RSL.Env) (choices : NMX_R4_Authentication.Choices)
 (v : r1_pool_adapter.ValidatedAsqa) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) :
 NMX_R8_Factor241.afterValidate (NMX_R8_Std241.ops env) (NMX_R8_Children241.grouped choices) v accounts =
 source env choices v accounts := by
 unfold NMX_R8_Factor241.afterValidate source NMS_R2N_RawTry.literal
 apply congrArg (RSL.Spec.bind _)
 funext acc0
 apply congrArg (RSL.Spec.bind _)
 funext firstReply
 apply congrArg (RSL.Spec.bind _)
 funext firstFlow
 cases firstFlow with
 | Break residual => rfl
 | Continue proof =>
   dsimp only
   apply congrArg (RSL.Spec.bind _)
   funext acc6
   apply congrArg (RSL.Spec.bind _)
   funext secondReply
   apply congrArg (RSL.Spec.bind _)
   funext secondFlow
   cases secondFlow <;> rfl
#print axioms factor
end NMX_R8_AfterFactor241
end
