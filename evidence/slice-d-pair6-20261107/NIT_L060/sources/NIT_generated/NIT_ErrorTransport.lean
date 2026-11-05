import NIT_Cuts
set_option autoImplicit false
namespace AspisR1.NIT_ErrorTransport
open Aeneas Aeneas.Std Result NIT_Cuts
abbrev NativeError := FIo_Native.verifier.Error
abbrev NativeReply (T : Type) := core.result.Result T NativeError

theorem error_injective : Function.Injective FIo_Install.error := by
 intro x y h
 cases x <;> cases y <;> simp_all [FIo_Install.error]

def unitReply {T : Type} : NativeReply T → Reply Unit
 | .Ok _ => .Ok ()
 | .Err e => .Err (FIo_Install.error e)

def reply : NativeReply E → Reply FE
 | .Ok x => .Ok (FIo_Install.fromE x)
 | .Err e => .Err (FIo_Install.error e)

def full : Result (NativeReply E) → Result (Reply FE)
 | .ok r=>.ok (reply r) | .fail e=>.fail e | .div=>.div

theorem fromE_injective : Function.Injective FIo_Install.fromE := by
 intro x y h
 exact congrArg FIo_Install.toE h

theorem reply_injective : Function.Injective reply := by
 intro x y h
 cases x with
 | Err e =>
  cases y with
  | Err f => exact congrArg core.result.Result.Err (error_injective (core.result.Result.Err.inj h))
  | Ok b => cases h
 | Ok a =>
  cases y with
  | Err f => cases h
  | Ok b => exact congrArg core.result.Result.Ok (fromE_injective (core.result.Result.Ok.inj h))

theorem full_injective : Function.Injective full := by
 intro x y h
 cases x with
 | ok a =>
  cases y with
  | ok b => exact congrArg Result.ok (reply_injective (Result.ok.inj h))
  | fail e => cases h
  | div => cases h
 | fail e =>
  cases y with
  | ok b => cases h
  | fail f => cases h;rfl
  | div => cases h
 | div =>
  cases y with
  | ok b => cases h
  | fail e => cases h
  | div => rfl

/-- Native cut's finite error code agrees with NIQ's lossless root encoding. -/
def nativeCode (e : NativeError) : Nat := NIQ_ResultEncoding.error (FIo_Install.error e)

theorem nativeCode_injective : Function.Injective nativeCode := by
 intro x y same
 exact error_injective (NIQ_ResultEncoding.error_injective same)

#print axioms error_injective
#print axioms fromE_injective
#print axioms reply_injective
#print axioms full_injective
#print axioms nativeCode_injective
end AspisR1.NIT_ErrorTransport
