import R1Z.BuilderForestStdPort

/-! Small inversion at the exact Option -> Rust Result -> Try boundary.
No source callee is evaluated; the payload type remains arbitrary. -/
set_option autoImplicit false
namespace R1Z.PV_Src_ResultControl
open Aeneas Aeneas.Std Result

theorem option_continue {α ε : Type} {o : Option α} {e : ε}
    {r : core.result.Result α ε} {b : α}
    (ho : BuilderForestStd.okOr o e = ok r)
    (hb : core.result.Result.Insts.CoreOpsTry.branch r = ok (.Continue b)) :
    o = some b := by
  cases o with
  | none =>
    have he : r = .Err e := (Result.ok.inj ho).symm
    subst r
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at hb
    cases hb
  | some a =>
    have he : r = .Ok a := (Result.ok.inj ho).symm
    subst r
    have hab : a = b :=
      core.ops.control_flow.ControlFlow.Continue.inj (Result.ok.inj hb)
    exact congrArg some hab

theorem error_ne_ok {α ε : Type} (e : ε) (a : α) :
    (ok (.Err e) : Result (core.result.Result α ε)) ≠ ok (.Ok a) := by
  intro h
  cases h

theorem same_residual_ne_ok {α ε : Type}
    (r : core.result.Result core.convert.Infallible ε) (a : α) :
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      α (core.convert.FromSame ε) r ≠ ok (.Ok a) := by
  intro h
  cases r with
  | Ok bad => cases bad
  | Err e =>
    change (ok (.Err e) : Result (core.result.Result α ε)) = ok (.Ok a) at h
    cases h

#print axioms option_continue
#print axioms error_ne_ok
#print axioms same_residual_ne_ok
end R1Z.PV_Src_ResultControl
