import NLJ_ObservedDenote
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
  all_goals simp only [step,denote,advance]
  all_goals simp only [NLJ_Monad.bind_assoc,NLJ_Monad.bind_pure]
  all_goals first
  | rfl
  | (unfold S1SemanticCode.verify; simp only [NLJ_Monad.bind_assoc,NLJ_Monad.bind_pure]; rfl)
#print axioms source_step
end AspisR1.NLJ_Observed
end
