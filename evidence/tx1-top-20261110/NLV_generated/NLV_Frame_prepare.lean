import NLV_Leaves
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLV_Tree
open Aeneas Aeneas.Std Result AspisR1CurrentCaller NLJ_Tx1
open CheckpointBytes5Effect (Code)
theorem frame_prepare (cfg : Configuration) (i : Input) (g : Scratch) :
 AllLeaves (FramePost ⟨i,.prepare g⟩) (step cfg ⟨i,.prepare g⟩) := by
 dsimp only [step]
 simp only [Bind.bind,Pure.pure]
 repeat' first
 | (apply leaves_bind; intro reply; cases reply)
 | (split)
 | (simp only [AllLeaves,FramePost,advance,rank,nextOrError])
 | trivial
 | decide
#print axioms frame_prepare
theorem progress_prepare (cfg : Configuration) (i : Input) (g : Scratch) :
 AllLeaves (ProgressPost ⟨i,.prepare g⟩) (step cfg ⟨i,.prepare g⟩) := by
 dsimp only [step]
 simp only [Bind.bind,Pure.pure]
 repeat' first
 | (apply leaves_bind; intro reply; cases reply)
 | (split)
 | (simp only [AllLeaves,ProgressPost,advance,rank,nextOrError])
 | trivial
 | decide
#print axioms progress_prepare
end AspisR1.NLV_Tree
end
