import NLV_Continuation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLV_Tree
open Aeneas Aeneas.Std Result AspisR1CurrentCaller NLJ_Tx1
open CheckpointBytes5Effect (Code)
theorem step_zero (cfg : Configuration) (i : Input)  :
 CheckpointBytes5Effect.bind (step cfg ⟨i,.zero⟩) (continuation cfg) =
 denote cfg ⟨i,.zero⟩ := by
 dsimp only [step,advance,denote,suffix_zero,nextOrError,continuation]
 simp only [Bind.bind,Pure.pure,NLV_Algebra.assoc,CheckpointBytes5Effect.bind]
 all_goals repeat' first
 | rfl
 | (apply NLV_Algebra.same; intro reply; cases reply)
 | (split <;> simp only [Bind.bind,Pure.pure,CheckpointBytes5Effect.bind])
#print axioms step_zero
end AspisR1.NLV_Tree
end
