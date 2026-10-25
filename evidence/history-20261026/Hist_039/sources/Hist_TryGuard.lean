import AdapterRwCuts
set_option autoImplicit false
namespace AspisR1.Hist_TryGuard
open Aeneas Aeneas.Std Result
abbrev PE := AdapterRw.solana_program_error.ProgramError

def thenTry {A B : Type} (r : Result (core.result.Result A PE))
    (tail : A → Result (core.result.Result B PE)) : Result (core.result.Result B PE) := do
  let inner ← r
  let cf ← core.result.Result.Insts.CoreOpsTry.branch inner
  match cf with
  | .Continue value => tail value
  | .Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      B (core.convert.FromSame PE) residual

/-- Source '?' inversion, retaining the SAME successful continuation. -/
theorem success {A B : Type} (r : Result (core.result.Result A PE))
    (tail : A → Result (core.result.Result B PE)) (out : B)
    (accepted : thenTry r tail = ok (.Ok out)) :
    ∃ value, r = ok (.Ok value) ∧ tail value = ok (.Ok out) := by
  cases r with
  | fail e => cases accepted
  | div => cases accepted
  | ok inner =>
    cases inner with
    | Err e => cases accepted
    | Ok value => exact ⟨value,rfl,accepted⟩

#print axioms success
end AspisR1.Hist_TryGuard
