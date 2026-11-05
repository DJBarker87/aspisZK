import NIG_FinishPacket
set_option autoImplicit false
namespace NIQ_ResultEncoding
open Aeneas Aeneas.Std AspisR1Stage2

def error : verifier.Error → Nat
 | .Parse => 0 | .Semantic => 1 | .Transcript => 2 | .Relation => 3
 | .Merkle => 4 | .Query => 5 | .Checkpoint => 6 | .Allocation => 7

theorem error_injective : Function.Injective error := by
 intro x y h
 cases x <;> cases y <;> simp_all [error]

def returning {T : Type} : core.result.Result T verifier.Error → Except Nat T
 | .Ok value => .ok value
 | .Err e => .error (error e)

theorem returning_injective {T : Type} : Function.Injective (@returning T) := by
 intro x y h
 cases x with
 | Err e =>
   cases y with
   | Err f => exact congrArg core.result.Result.Err (error_injective (Except.error.inj h))
   | Ok b => cases h
 | Ok a =>
   cases y with
   | Err f => cases h
   | Ok b => exact congrArg core.result.Result.Ok (Except.ok.inj h)

/-- Preserve the outer abort/nonreturn boundary; the native returning record
alone does not encode a fail or div as a verifier Err. -/
def full {T : Type} : Result (core.result.Result T verifier.Error) → Result (Except Nat T)
 | .ok r => .ok (returning r)
 | .fail e => .fail e
 | .div => .div

theorem full_injective {T : Type} : Function.Injective (@full T) := by
 intro x y h
 cases x with
 | ok a =>
   cases y with
   | ok b => exact congrArg Result.ok (returning_injective (Result.ok.inj h))
   | fail e => cases h
   | div => cases h
 | fail e =>
   cases y with
   | ok b => cases h
   | fail f => cases h; rfl
   | div => cases h
 | div =>
   cases y with
   | ok b => cases h
   | fail e => cases h
   | div => rfl

#print axioms error_injective
#print axioms returning_injective
#print axioms full_injective
end NIQ_ResultEncoding
