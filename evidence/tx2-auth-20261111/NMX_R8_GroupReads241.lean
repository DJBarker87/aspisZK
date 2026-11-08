import NMX_R8_GroupEncode241
set_option autoImplicit false
noncomputable section
namespace NMX_R8_GroupReads241
open Aeneas Aeneas.Std Result AdapterRw

theorem source (choices : NMX_R4_Authentication.Choices) (ops : Ops)
 (val : r1_pool_adapter.ValidatedAsqa) (proof checkpoint : Slice U8) :
 NMX_R8_OldFactor241.afterReads ops (NMX_R8_Children241.original choices) val proof checkpoint =
 NMX_R8_Factor241.afterReads ops (NMX_R8_Children241.grouped choices) val proof checkpoint := by
 unfold NMX_R8_OldFactor241.afterReads NMX_R8_Factor241.afterReads
 apply congrArg (RSL.Spec.bind _)
 funext start
 apply congrArg (RSL.Spec.bind _)
 funext endOption
 apply congrArg (RSL.Spec.bind _)
 funext endReply
 apply congrArg (RSL.Spec.bind _)
 funext flow
 cases flow with
 | Break residual => rfl
 | Continue finish =>
   dsimp only
   split
   · rfl
   · simp only [NMX_R8_GroupEncode241.source]
     exact NMX_R8_CodecGroup.context val.statement _
#print axioms source
end NMX_R8_GroupReads241
end
