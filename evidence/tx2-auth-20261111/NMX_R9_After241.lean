import NMX_R9_Children241
import NMX_R8_After241
import NMX_R8_GroupValidate241
set_option autoImplicit false
noncomputable section
namespace NMX_R9_After241
open Aeneas Aeneas.Std Result AdapterRw

theorem fixed (choices : NMX_R4_Authentication.Choices) (ops : Ops)
 (v : r1_pool_adapter.ValidatedAsqa) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) :
 NMX_R8_Factor241.afterValidate ops (NMX_R9_Children241.grouped choices) v accounts =
 NMX_R8_Factor241.afterValidate ops (NMX_R8_Children241.grouped choices) v accounts := by
 unfold NMX_R8_Factor241.afterValidate NMX_R8_Factor241.afterReads NMX_R8_Factor241.afterEncode
 rfl

theorem grouped (choices : NMX_R4_Authentication.Choices) (ops : Ops)
 (v : r1_pool_adapter.ValidatedAsqa) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) :
 NMX_R8_OldFactor241.afterValidate ops (NMX_R9_Children241.original choices) v accounts =
 NMX_R8_Factor241.afterValidate ops (NMX_R9_Children241.grouped choices) v accounts := by
 calc
  _ = NMX_R8_OldFactor241.afterValidate ops (NMX_R8_Children241.original choices) v accounts := by
   unfold NMX_R8_OldFactor241.afterValidate NMX_R8_OldFactor241.afterReads NMX_R8_OldFactor241.afterEncode
   rfl
  _ = NMX_R8_Factor241.afterValidate ops (NMX_R8_Children241.grouped choices) v accounts :=
   NMX_R8_GroupValidate241.source choices ops v accounts
  _ = _ := (fixed choices ops v accounts).symm

theorem full (env : RSL.Env) (choices : NMX_R4_Authentication.Choices)
 (v : r1_pool_adapter.ValidatedAsqa) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (length : v.proof_length = 57607#usize) :
 NMS_R2N_Interpreted.Simulates (NMS_R2N_RSLError.reply id)
  (NMX_R8_Factor241.afterValidate (NMX_R8_Std241.ops env) (NMX_R9_Children241.grouped choices) v accounts)
  (NMX_R8_After241.model (NMX_R5_AfterAuth242.value v) (NMS_R2N_RSLPoolCarriers.accounts accounts)) := by
 rw [fixed]
 exact NMX_R8_After241.full env choices v accounts length
#print axioms fixed
#print axioms grouped
#print axioms full
end NMX_R9_After241
end
