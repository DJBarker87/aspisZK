import NMS_R2Code242Factor
import NMS_R2Tail242
set_option autoImplicit false
noncomputable section
namespace NMS_R2AfterAuthEq242
open Aeneas Aeneas.Std AdapterRw
open NMS_R2Tail242 NMS_R2N_Interpreted
theorem factor (devnet : Bool) (q : Request) (auth : Auth)
 (accounts : Slice r1_pool_adapter.owned.OwnedAccount) :
 NMS_R2Code242Factor.afterAuth (NMS_R2N_Native242Children.children devnet) q auth accounts =
 RSL.Spec.bind (RSL.Spec.pure accounts.val.head?) fun first =>
 NMS_R2N_RawTry.literal
  (NMS_R2N_Interpreted.liftResult
   (core.option.Option.ok_or first solana_program_error.ProgramError.NotEnoughAccountKeys))
  (NMS_R2Tail242.raw q auth) := by
 unfold NMS_R2Code242Factor.afterAuth NMS_R2Tail242.raw NMS_R2N_RawTry.literal
 dsimp only [NMS_R2N_Native242Children.children]
 apply congrArg (RSL.Spec.bind _)
 funext first
 apply congrArg (RSL.Spec.bind _)
 funext firstReply
 apply congrArg (RSL.Spec.bind _)
 funext firstFlow
 cases firstFlow with
 | Break residual => rfl
 | Continue value =>
   apply congrArg (RSL.Spec.bind _)
   funext reply1
   apply congrArg (RSL.Spec.bind _)
   funext dataFlow
   cases dataFlow with
   | Break residual => rfl
   | Continue value =>
     apply congrArg (RSL.Spec.bind _)
     funext reply3
     apply congrArg (RSL.Spec.bind _)
     funext scanFlow
     cases scanFlow with
     | Break residual => rfl
     | Continue value =>
       apply congrArg (RSL.Spec.bind _)
       funext reply5
       apply congrArg (RSL.Spec.bind _)
       funext statementFlow
       cases statementFlow with
       | Break residual => rfl
       | Continue value =>
         rfl

#print axioms factor
end NMS_R2AfterAuthEq242
