import NLV_Continuation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLV_Tree
open Aeneas Aeneas.Std Result AspisR1CurrentCaller NLJ_Tx1
open CheckpointBytes5Effect (Code)
theorem step_query (cfg : Configuration) (i : Input) (g : Scratch) (p : verifier.Prepared) (a : verifier.Accumulator) (geom : verifier.QueryGeometry) (pending : verifier.BatchedWeights) :
 CheckpointBytes5Effect.bind (step cfg ⟨i,.query g p a geom pending⟩) (continuation cfg) =
 denote cfg ⟨i,.query g p a geom pending⟩ := by
 dsimp only [step,advance,denote,suffix_query,nextOrError,continuation]
 simp only [Bind.bind,Pure.pure,NLV_Algebra.assoc,CheckpointBytes5Effect.bind]
 all_goals repeat' first
 | rfl
 | (apply NLV_Algebra.same; intro reply; cases reply)
 | (split <;> simp only [Bind.bind,Pure.pure,CheckpointBytes5Effect.bind])
#print axioms step_query
end AspisR1.NLV_Tree
end
