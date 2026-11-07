import NMT_345Carriers
set_option autoImplicit false
namespace NMT_345
open Aeneas Aeneas.Std Result
/-- Exact Ok recovery through a representation-only error map. No success
is assumed of the parent; this is used only inside its returning step case. -/
theorem map_ok_recover {A E F : Type} (f : E → F)
 (r : Result (core.result.Result A E)) (a : A)
 (h : mapOuter (mapCore id f) r = .ok (.Ok a)) : r = .ok (.Ok a) := by
 cases r with
 | fail e => cases h
 | div => cases h
 | ok r =>
  cases r with
  | Err e => cases h
  | Ok x =>
   have hx : x = a := core.result.Result.Ok.inj (Result.ok.inj h)
   subst x; rfl
#print axioms map_ok_recover
end NMT_345
