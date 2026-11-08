import NMX_R8_GroupReads241
set_option autoImplicit false
noncomputable section
namespace NMX_R8_GroupValidate241
open Aeneas Aeneas.Std Result AdapterRw

theorem source (choices : NMX_R4_Authentication.Choices) (ops : Ops)
 (val : r1_pool_adapter.ValidatedAsqa) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) :
 NMX_R8_OldFactor241.afterValidate ops (NMX_R8_Children241.original choices) val accounts =
 NMX_R8_Factor241.afterValidate ops (NMX_R8_Children241.grouped choices) val accounts := by
 unfold NMX_R8_OldFactor241.afterValidate NMX_R8_Factor241.afterValidate
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
   cases secondFlow with
   | Break residual => rfl
   | Continue checkpoint =>
     dsimp only
     exact NMX_R8_GroupReads241.source choices ops val proof checkpoint
#print axioms source
end NMX_R8_GroupValidate241
end
