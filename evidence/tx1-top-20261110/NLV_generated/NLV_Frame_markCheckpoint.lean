import NLV_Leaves
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLV_Tree
open Aeneas Aeneas.Std Result AspisR1CurrentCaller NLJ_Tx1
open CheckpointBytes5Effect (Code)
theorem frame_markCheckpoint (cfg : Configuration) (i : Input) (bytes : alloc.vec.Vec U8) :
 AllLeaves (FramePost ⟨i,.markCheckpoint bytes⟩) (step cfg ⟨i,.markCheckpoint bytes⟩) := by
 dsimp only [step]
 simp only [Bind.bind,Pure.pure]
 repeat' first
 | (apply leaves_bind; intro reply; cases reply)
 | (split)
 | (simp only [AllLeaves,FramePost,advance,rank,nextOrError])
 | trivial
 | decide
#print axioms frame_markCheckpoint
theorem progress_markCheckpoint (cfg : Configuration) (i : Input) (bytes : alloc.vec.Vec U8) :
 AllLeaves (ProgressPost ⟨i,.markCheckpoint bytes⟩) (step cfg ⟨i,.markCheckpoint bytes⟩) := by
 dsimp only [step]
 simp only [Bind.bind,Pure.pure]
 repeat' first
 | (apply leaves_bind; intro reply; cases reply)
 | (split)
 | (simp only [AllLeaves,ProgressPost,advance,rank,nextOrError])
 | trivial
 | decide
#print axioms progress_markCheckpoint
end AspisR1.NLV_Tree
end
