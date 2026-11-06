import NLV_Continuation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLV_Tree
open Aeneas Aeneas.Std Result AspisR1CurrentCaller NLJ_Tx1
open CheckpointBytes5Effect (Code)
theorem step_accumulator (cfg : Configuration) (i : Input) (g : Scratch) (p : verifier.Prepared) :
 CheckpointBytes5Effect.bind (step cfg ⟨i,.accumulator g p⟩) (continuation cfg) =
 denote cfg ⟨i,.accumulator g p⟩ := by
 dsimp only [step,advance,denote,suffix_accumulator,nextOrError,continuation]
 simp only [Bind.bind,Pure.pure,NLV_Algebra.assoc,CheckpointBytes5Effect.bind]
 all_goals repeat' first
 | rfl
 | (apply NLV_Algebra.same; intro reply; cases reply)
 | (split <;> simp only [Bind.bind,Pure.pure,CheckpointBytes5Effect.bind])
#print axioms step_accumulator
end AspisR1.NLV_Tree
end
