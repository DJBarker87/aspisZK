import NLV_Leaves
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLV_Tree
open Aeneas Aeneas.Std Result AspisR1CurrentCaller NLJ_Tx1
open CheckpointBytes5Effect (Code)
theorem frame_foldedUnwrap (cfg : Configuration) (i : Input) (g : Scratch) (p : verifier.Prepared) (a : verifier.Accumulator) (r : core.result.Result Root core.array.TryFromSliceError) :
 AllLeaves (FramePost ⟨i,.foldedUnwrap g p a r⟩) (step cfg ⟨i,.foldedUnwrap g p a r⟩) := by
 dsimp only [step]
 simp only [Bind.bind,Pure.pure]
 repeat' first
 | (apply leaves_bind; intro reply; cases reply)
 | (split)
 | (simp only [AllLeaves,FramePost,advance,rank,nextOrError])
 | trivial
 | decide
#print axioms frame_foldedUnwrap
theorem progress_foldedUnwrap (cfg : Configuration) (i : Input) (g : Scratch) (p : verifier.Prepared) (a : verifier.Accumulator) (r : core.result.Result Root core.array.TryFromSliceError) :
 AllLeaves (ProgressPost ⟨i,.foldedUnwrap g p a r⟩) (step cfg ⟨i,.foldedUnwrap g p a r⟩) := by
 dsimp only [step]
 simp only [Bind.bind,Pure.pure]
 repeat' first
 | (apply leaves_bind; intro reply; cases reply)
 | (split)
 | (simp only [AllLeaves,ProgressPost,advance,rank,nextOrError])
 | trivial
 | decide
#print axioms progress_foldedUnwrap
end AspisR1.NLV_Tree
end
