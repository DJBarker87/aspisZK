import NLJ_CodeRight
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_Observed
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code)
/-- Source control-flow identity for one occurrence, including every inner Err
and outer abort; there is no native observation or selected successful reply. -/
theorem source_step {H : Type} (s : State H) :
 denote s = (do
   let post ← step s
   match post with
   | .inl out => pure out
   | .inr after => denote after) := by
 cases s with
 | mk input locals =>
  cases locals
  all_goals dsimp only [step,denote,advance]
  all_goals try simp only [Bind.bind,Pure.pure,NLJ_Monad.bind_assoc,NLJ_Monad.bind_pure,NLJ_CodeRight.right]
  all_goals repeat' first
  | rfl
  | (apply NLJ_CodeRight.same; intro x; cases x)
  | (split <;> simp only [Bind.bind,Pure.pure,NLJ_Monad.bind_assoc,NLJ_Monad.bind_pure,NLJ_CodeRight.right])
  | (unfold S1SemanticCode.verify)

#print axioms source_step
end AspisR1.NLJ_Observed
end
