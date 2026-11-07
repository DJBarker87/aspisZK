import NLV_Continuation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLV_Tree
open Aeneas Aeneas.Std Result AspisR1CurrentCaller NLJ_Tx1
open CheckpointBytes5Effect (Code)
theorem step_returned (cfg : Configuration) (i : Input) (bytes : alloc.vec.Vec U8) :
 CheckpointBytes5Effect.bind (step cfg ⟨i,.returned bytes⟩) (continuation cfg) =
 denote cfg ⟨i,.returned bytes⟩ := by
 dsimp only [step,advance,denote,suffix_returned,nextOrError,continuation]
 simp only [Bind.bind,Pure.pure,NLV_Algebra.assoc,CheckpointBytes5Effect.bind]
 all_goals repeat' first
 | rfl
 | (apply NLV_Algebra.same; intro reply; cases reply)
 | (split <;> simp only [Bind.bind,Pure.pure,CheckpointBytes5Effect.bind])
#print axioms step_returned
end AspisR1.NLV_Tree
end
