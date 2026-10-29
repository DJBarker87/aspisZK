import R1Z.PV_RunJoin_PublicationResult55
set_option autoImplicit false
namespace R1Z.PV_RunJoin_PublicationSuccess55
open Aeneas Aeneas.Std Result PV_RunJoin_ResultRelation55
open PV_RunJoin_PublicationResult55

theorem complete {A B C E : Type} (decode : A → C) (encode : B → C) (fallback : E)
    (source : Result (core.result.Result A E)) (published : Option B)
    (h : ∀ a,source=ok (.Ok a) → some (decode a)=published.map encode) :
    Rel (CoreRel (fun a b => decode a=encode b)) source (install fallback source published) := by
  cases hs : source with
  | fail e => exact .fail e
  | div => exact .div
  | ok r =>
    cases r with
    | Err e => exact .ok (.err e)
    | Ok a => exact PV_RunJoin_PublicationResult55.complete decode encode fallback _ published (h a hs)
#print axioms complete
end R1Z.PV_RunJoin_PublicationSuccess55
