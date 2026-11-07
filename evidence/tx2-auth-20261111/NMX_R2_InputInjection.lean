import NMX_R2_ErrorInverse
import NMX_R2_KeyCarrier
import NMX_R2_CallArguments
set_option autoImplicit false
namespace NMX_R2_InputInjection
open Aeneas Aeneas.Std AdapterRw NMX_R2_Carrier NMX_R2_ScalarCarrier

theorem reply {A B : Type} (encode : A → B) (injective : Function.Injective encode) :
 Function.Injective (NMX_R2_Carrier.reply encode) := by
 intro r s same
 cases r with
 | Ok a =>
   cases s with
   | Ok b => exact congrArg core.result.Result.Ok (injective (Except.ok.inj same))
   | Err e => cases same
 | Err a =>
   cases s with
   | Ok b => cases same
   | Err b => exact congrArg core.result.Result.Err (NMX_R2_ErrorInverse.injective (Except.error.inj same))

theorem vector : Function.Injective (fun v : alloc.vec.Vec U8 => v.val.map byte) := by
 intro a b same
 apply Subtype.ext
 exact (List.map_inj_right (fun x y h => byte_injective h)).mp same

/-- Every field of the frozen OwnedAccount input is retained, including the
complete String-bearing deferred errors and arbitrary successful byte values. -/
theorem account : Function.Injective NMX_R2_Carrier.account := by
 intro a b same
 cases a with
 | mk ak ao aSign aWrite aExec al ab =>
   cases b with
   | mk bk bo bSign bWrite bExec bl bb =>
     have hk := NMX_R2_KeyCarrier.key_injective (congrArg RSL.OwnedAccount.key same)
     have ho := NMX_R2_KeyCarrier.key_injective (congrArg RSL.OwnedAccount.owner same)
     have hs : aSign = bSign := congrArg RSL.OwnedAccount.is_signer same
     have hw : aWrite = bWrite := congrArg RSL.OwnedAccount.is_writable same
     have he : aExec = bExec := congrArg RSL.OwnedAccount.executable same
     have hl := reply (fun n : Usize => n.val) (fun x y h => UScalar.eq_of_val_eq h)
      (congrArg RSL.OwnedAccount.length same)
     have hb := reply (fun v : alloc.vec.Vec U8 => v.val.map byte) vector
      (congrArg RSL.OwnedAccount.bytes same)
     cases hk; cases ho; cases hs; cases hw; cases he; cases hl; cases hb
     rfl
#print axioms reply
#print axioms vector
#print axioms account
end NMX_R2_InputInjection
