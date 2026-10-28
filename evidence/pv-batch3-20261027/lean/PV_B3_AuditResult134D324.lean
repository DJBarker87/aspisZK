import PV_B3_MaskDictionary134
namespace PV_B3_AuditResult134D324
open Aeneas Aeneas.Std Result PV_B3_MaskDictionary134
set_option autoImplicit false

def restoreError : OldError → NewError
  | .Shape => .Shape
  | .EndpointCapacity row => .EndpointCapacity row

def restore : Result OldFinal → Result NewFinal
  | .ok (.Ok m) => .ok (.Ok m)
  | .ok (.Err e) => .ok (.Err (restoreError e))
  | .fail e => .fail e
  | .div => .div

theorem error_roundtrip (e : NewError) : restoreError (error e) = e := by
  cases e <;> rfl

theorem reverse_error_roundtrip (e : OldError) : error (restoreError e) = e := by
  cases e <;> rfl

theorem roundtrip (r : Result NewFinal) : restore (translate r) = r := by
  cases r with
  | fail e => rfl
  | div => rfl
  | ok value =>
    cases value with
    | Ok m => rfl
    | Err e => simp only [translate, restore, error_roundtrip]

theorem reverse_roundtrip (r : Result OldFinal) : translate (restore r) = r := by
  cases r with
  | fail e => rfl
  | div => rfl
  | ok value =>
    cases value with
    | Ok m => rfl
    | Err e => simp only [translate, restore, reverse_error_roundtrip]

theorem injective : Function.Injective translate := by
  intro a b h
  have eq := congrArg restore h
  simpa only [roundtrip] using eq

theorem no_hidden_success (r : Result NewFinal) (m : Array U16 64#usize) :
    translate r = ok (.Ok m) ↔ r = ok (.Ok m) := by
  constructor
  · intro h
    have eq := congrArg restore h
    simpa only [roundtrip, restore] using eq
  · intro h
    rw [h]
    rfl

#print axioms restoreError
#print axioms restore
#print axioms error_roundtrip
#print axioms reverse_error_roundtrip
#print axioms roundtrip
#print axioms reverse_roundtrip
#print axioms injective
#print axioms no_hidden_success
end PV_B3_AuditResult134D324
