import NLV_Leaves
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLV_Tree
open Aeneas Aeneas.Std Result AspisR1CurrentCaller NLJ_Tx1
open CheckpointBytes5Effect (Code)
theorem frame_finishPending (cfg : Configuration) (i : Input) (p : verifier.Prepared) (a : verifier.Accumulator) (pending : verifier.BatchedWeights) :
 AllLeaves (FramePost ⟨i,.finishPending p a pending⟩) (step cfg ⟨i,.finishPending p a pending⟩) := by
 dsimp only [step]
 simp only [Bind.bind,Pure.pure]
 repeat' first
 | (apply leaves_bind; intro reply; cases reply)
 | (split)
 | (simp only [AllLeaves,FramePost,advance,rank,nextOrError])
 | trivial
 | decide
#print axioms frame_finishPending
theorem progress_finishPending (cfg : Configuration) (i : Input) (p : verifier.Prepared) (a : verifier.Accumulator) (pending : verifier.BatchedWeights) :
 AllLeaves (ProgressPost ⟨i,.finishPending p a pending⟩) (step cfg ⟨i,.finishPending p a pending⟩) := by
 dsimp only [step]
 simp only [Bind.bind,Pure.pure]
 repeat' first
 | (apply leaves_bind; intro reply; cases reply)
 | (split)
 | (simp only [AllLeaves,ProgressPost,advance,rank,nextOrError])
 | trivial
 | decide
#print axioms progress_finishPending
end AspisR1.NLV_Tree
end
