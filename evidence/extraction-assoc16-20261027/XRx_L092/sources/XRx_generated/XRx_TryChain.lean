import XRx_StageRules
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XRx_TryChain
/-- Explicit source Try branching is a first-stop continuation. -/
theorem source {E S O : Type} (r : core.result.Result S E)
 (k : S → Result (core.result.Result O E)) :
 (do
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | .Continue s => k s
  | .Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      O (core.convert.FromSame E) residual) =
 (match r with | .Err e => ok (core.result.Result.Err e) | .Ok s => k s) := by
 cases r <;> rfl

/-- Tuple destruction and projections have the SAME carrier, including a
state carrying a transcript/chronological call history. -/
theorem pair {A B C : Type} (p : A × B) (f : A → B → C) :
 Prod.casesOn p f=f p.1 p.2 := by
 cases p
 rfl
#print axioms source
#print axioms pair
end XRx_TryChain
