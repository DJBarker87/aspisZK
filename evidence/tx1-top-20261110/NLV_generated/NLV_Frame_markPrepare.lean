import NLV_Leaves
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLV_Tree
open Aeneas Aeneas.Std Result AspisR1CurrentCaller NLJ_Tx1
open CheckpointBytes5Effect (Code)
theorem frame_markPrepare (cfg : Configuration) (i : Input) (g : Scratch) (p : verifier.Prepared) (a : verifier.Accumulator) :
 AllLeaves (FramePost ⟨i,.markPrepare g p a⟩) (step cfg ⟨i,.markPrepare g p a⟩) := by
 dsimp only [step]
 simp only [Bind.bind,Pure.pure]
 repeat' first
 | (apply leaves_bind; intro reply; cases reply)
 | (split)
 | (simp only [AllLeaves,FramePost,advance,rank,nextOrError])
 | trivial
 | decide
#print axioms frame_markPrepare
theorem progress_markPrepare (cfg : Configuration) (i : Input) (g : Scratch) (p : verifier.Prepared) (a : verifier.Accumulator) :
 AllLeaves (ProgressPost ⟨i,.markPrepare g p a⟩) (step cfg ⟨i,.markPrepare g p a⟩) := by
 dsimp only [step]
 simp only [Bind.bind,Pure.pure]
 repeat' first
 | (apply leaves_bind; intro reply; cases reply)
 | (split)
 | (simp only [AllLeaves,ProgressPost,advance,rank,nextOrError])
 | trivial
 | decide
#print axioms progress_markPrepare
end AspisR1.NLV_Tree
end
