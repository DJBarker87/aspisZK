import NHT_ResultPort
set_option autoImplicit false
namespace NHT_ResultSuccess
open Aeneas Aeneas.Std Result
/-- Port inversion preserves the SAME payload and excludes error/fail/div. -/
theorem source {A : Type} (m : Result (core.result.Result A NHT_ResultPort.SourceError))
 (a : A) (returned : NHT_ResultPort.action m=ok (.Ok a)) : m=ok (.Ok a) := by
 cases m with
 | fail e => cases returned
 | div => cases returned
 | ok reply =>
   cases reply with
   | Err e => cases returned
   | Ok value =>
     have same := core.result.Result.Ok.inj (Result.ok.inj returned)
     subst value
     rfl
#print axioms source
end NHT_ResultSuccess
