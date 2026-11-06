import NLV_Leaves
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLV_Tree
open Aeneas Aeneas.Std Result AspisR1CurrentCaller NLJ_Tx1
open CheckpointBytes5Effect (Code)
theorem frame_returned (cfg : Configuration) (i : Input) (bytes : alloc.vec.Vec U8) :
 AllLeaves (FramePost ⟨i,.returned bytes⟩) (step cfg ⟨i,.returned bytes⟩) := by
 dsimp only [step]
 simp only [Bind.bind,Pure.pure]
 repeat' first
 | (apply leaves_bind; intro reply; cases reply)
 | (split)
 | (simp only [AllLeaves,FramePost,advance,rank,nextOrError])
 | trivial
 | decide
#print axioms frame_returned
theorem progress_returned (cfg : Configuration) (i : Input) (bytes : alloc.vec.Vec U8) :
 AllLeaves (ProgressPost ⟨i,.returned bytes⟩) (step cfg ⟨i,.returned bytes⟩) := by
 dsimp only [step]
 simp only [Bind.bind,Pure.pure]
 repeat' first
 | (apply leaves_bind; intro reply; cases reply)
 | (split)
 | (simp only [AllLeaves,ProgressPost,advance,rank,nextOrError])
 | trivial
 | decide
#print axioms progress_returned
end AspisR1.NLV_Tree
end
