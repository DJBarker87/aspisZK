import NLV_Leaves
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLV_Tree
open Aeneas Aeneas.Std Result AspisR1CurrentCaller NLJ_Tx1
open CheckpointBytes5Effect (Code)
theorem frame_query (cfg : Configuration) (i : Input) (g : Scratch) (p : verifier.Prepared) (a : verifier.Accumulator) (geom : verifier.QueryGeometry) (pending : verifier.BatchedWeights) :
 AllLeaves (FramePost ⟨i,.query g p a geom pending⟩) (step cfg ⟨i,.query g p a geom pending⟩) := by
 dsimp only [step]
 simp only [Bind.bind,Pure.pure]
 repeat' first
 | (apply leaves_bind; intro reply; cases reply)
 | (split)
 | (simp only [AllLeaves,FramePost,advance,rank,nextOrError])
 | trivial
 | decide
#print axioms frame_query
theorem progress_query (cfg : Configuration) (i : Input) (g : Scratch) (p : verifier.Prepared) (a : verifier.Accumulator) (geom : verifier.QueryGeometry) (pending : verifier.BatchedWeights) :
 AllLeaves (ProgressPost ⟨i,.query g p a geom pending⟩) (step cfg ⟨i,.query g p a geom pending⟩) := by
 dsimp only [step]
 simp only [Bind.bind,Pure.pure]
 repeat' first
 | (apply leaves_bind; intro reply; cases reply)
 | (split)
 | (simp only [AllLeaves,ProgressPost,advance,rank,nextOrError])
 | trivial
 | decide
#print axioms progress_query
end AspisR1.NLV_Tree
end
