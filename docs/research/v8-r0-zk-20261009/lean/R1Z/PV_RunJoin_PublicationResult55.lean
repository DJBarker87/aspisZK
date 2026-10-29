import R1Z.PV_RunJoin_ResultRelation55
set_option autoImplicit false
namespace R1Z.PV_RunJoin_PublicationResult55
open Aeneas Aeneas.Std Result PV_RunJoin_ResultRelation55

def view {A C E : Type} (decode : A → C) : Result (core.result.Result A E) → Option C
  | .ok (.Ok a) => some (decode a)
  | _ => none

def install {A B E : Type} (fallback : E) (source : Result (core.result.Result A E))
    (published : Option B) : Result (core.result.Result B E) :=
  match source with
  | .fail e => .fail e
  | .div => .div
  | .ok (.Err e) => .ok (.Err e)
  | .ok (.Ok _) => match published with
    | some p => .ok (.Ok p)
    | none => .ok (.Err fallback)

theorem complete {A B C E : Type} (decode : A → C) (encode : B → C) (fallback : E)
    (source : Result (core.result.Result A E)) (published : Option B)
    (h : view decode source=published.map encode) :
    Rel (CoreRel (fun a b => decode a=encode b)) source (install fallback source published) := by
  cases source with
  | fail e => exact .fail e
  | div => exact .div
  | ok r =>
    cases r with
    | Err e => exact .ok (.err e)
    | Ok a =>
      cases published with
      | none => cases h
      | some b => exact .ok (.ok (Option.some.inj h))
#print axioms view
#print axioms install
#print axioms complete
end R1Z.PV_RunJoin_PublicationResult55
