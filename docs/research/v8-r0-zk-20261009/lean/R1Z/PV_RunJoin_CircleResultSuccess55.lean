import R1Z.ProverRwFullFuns
set_option autoImplicit false
namespace R1Z.PV_RunJoin_CircleResultSuccess55
open Aeneas Aeneas.Std Result

theorem complete {P A T E : Type} (parsed : Result (core.result.Result P E))
    (q actual : A) (before after actualAfter : T)
    (success : (do
      let r ← parsed
      match r with
      | .Err e => ok (core.result.Result.Err e,before)
      | .Ok _ => ok (core.result.Result.Ok q,after))=ok (core.result.Result.Ok actual,actualAfter)) :
    actual=q ∧ actualAfter=after := by
  cases parsed with
  | fail e => cases success
  | div => cases success
  | ok r =>
    cases r with
    | Err e => cases success
    | Ok p =>
      cases success
      exact ⟨rfl,rfl⟩
#print axioms complete
end R1Z.PV_RunJoin_CircleResultSuccess55
