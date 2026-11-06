import NLV_Leaves
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLV_Tree
open Aeneas Aeneas.Std Result AspisR1CurrentCaller NLJ_Tx1
open CheckpointBytes5Effect (Code)
theorem frame_markMerkle (cfg : Configuration) (i : Input) (g : Scratch) (p : verifier.Prepared) (a : verifier.Accumulator) :
 AllLeaves (FramePost ⟨i,.markMerkle g p a⟩) (step cfg ⟨i,.markMerkle g p a⟩) := by
 dsimp only [step]
 simp only [Bind.bind,Pure.pure]
 repeat' first
 | (apply leaves_bind; intro reply; cases reply)
 | (split)
 | (simp only [AllLeaves,FramePost,advance,rank,nextOrError])
 | trivial
 | decide
#print axioms frame_markMerkle
theorem progress_markMerkle (cfg : Configuration) (i : Input) (g : Scratch) (p : verifier.Prepared) (a : verifier.Accumulator) :
 AllLeaves (ProgressPost ⟨i,.markMerkle g p a⟩) (step cfg ⟨i,.markMerkle g p a⟩) := by
 dsimp only [step]
 simp only [Bind.bind,Pure.pure]
 repeat' first
 | (apply leaves_bind; intro reply; cases reply)
 | (split)
 | (simp only [AllLeaves,ProgressPost,advance,rank,nextOrError])
 | trivial
 | decide
#print axioms progress_markMerkle
end AspisR1.NLV_Tree
end
