import NLV_Leaves
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLV_Tree
open Aeneas Aeneas.Std Result AspisR1CurrentCaller NLJ_Tx1
open CheckpointBytes5Effect (Code)
theorem frame_parse (cfg : Configuration) (i : Input)  :
 AllLeaves (FramePost ⟨i,.parse⟩) (step cfg ⟨i,.parse⟩) := by
 dsimp only [step]
 simp only [Bind.bind,Pure.pure]
 repeat' first
 | (apply leaves_bind; intro reply; cases reply)
 | (split)
 | (simp only [AllLeaves,FramePost,advance,rank,nextOrError])
 | trivial
 | decide
#print axioms frame_parse
theorem progress_parse (cfg : Configuration) (i : Input)  :
 AllLeaves (ProgressPost ⟨i,.parse⟩) (step cfg ⟨i,.parse⟩) := by
 dsimp only [step]
 simp only [Bind.bind,Pure.pure]
 repeat' first
 | (apply leaves_bind; intro reply; cases reply)
 | (split)
 | (simp only [AllLeaves,ProgressPost,advance,rank,nextOrError])
 | trivial
 | decide
#print axioms progress_parse
theorem frame_scan (cfg : Configuration) (i : Input)  :
 AllLeaves (FramePost ⟨i,.scan⟩) (step cfg ⟨i,.scan⟩) := by
 dsimp only [step]
 simp only [Bind.bind,Pure.pure]
 repeat' first
 | (apply leaves_bind; intro reply; cases reply)
 | (split)
 | (simp only [AllLeaves,FramePost,advance,rank,nextOrError])
 | trivial
 | decide
#print axioms frame_scan
theorem progress_scan (cfg : Configuration) (i : Input)  :
 AllLeaves (ProgressPost ⟨i,.scan⟩) (step cfg ⟨i,.scan⟩) := by
 dsimp only [step]
 simp only [Bind.bind,Pure.pure]
 repeat' first
 | (apply leaves_bind; intro reply; cases reply)
 | (split)
 | (simp only [AllLeaves,ProgressPost,advance,rank,nextOrError])
 | trivial
 | decide
#print axioms progress_scan
theorem frame_markParsed (cfg : Configuration) (i : Input)  :
 AllLeaves (FramePost ⟨i,.markParsed⟩) (step cfg ⟨i,.markParsed⟩) := by
 dsimp only [step]
 simp only [Bind.bind,Pure.pure]
 repeat' first
 | (apply leaves_bind; intro reply; cases reply)
 | (split)
 | (simp only [AllLeaves,FramePost,advance,rank,nextOrError])
 | trivial
 | decide
#print axioms frame_markParsed
theorem progress_markParsed (cfg : Configuration) (i : Input)  :
 AllLeaves (ProgressPost ⟨i,.markParsed⟩) (step cfg ⟨i,.markParsed⟩) := by
 dsimp only [step]
 simp only [Bind.bind,Pure.pure]
 repeat' first
 | (apply leaves_bind; intro reply; cases reply)
 | (split)
 | (simp only [AllLeaves,ProgressPost,advance,rank,nextOrError])
 | trivial
 | decide
#print axioms progress_markParsed
theorem frame_zero (cfg : Configuration) (i : Input)  :
 AllLeaves (FramePost ⟨i,.zero⟩) (step cfg ⟨i,.zero⟩) := by
 dsimp only [step]
 simp only [Bind.bind,Pure.pure]
 repeat' first
 | (apply leaves_bind; intro reply; cases reply)
 | (split)
 | (simp only [AllLeaves,FramePost,advance,rank,nextOrError])
 | trivial
 | decide
#print axioms frame_zero
theorem progress_zero (cfg : Configuration) (i : Input)  :
 AllLeaves (ProgressPost ⟨i,.zero⟩) (step cfg ⟨i,.zero⟩) := by
 dsimp only [step]
 simp only [Bind.bind,Pure.pure]
 repeat' first
 | (apply leaves_bind; intro reply; cases reply)
 | (split)
 | (simp only [AllLeaves,ProgressPost,advance,rank,nextOrError])
 | trivial
 | decide
#print axioms progress_zero
theorem frame_prepare (cfg : Configuration) (i : Input) (g : Scratch) :
 AllLeaves (FramePost ⟨i,.prepare g⟩) (step cfg ⟨i,.prepare g⟩) := by
 dsimp only [step]
 simp only [Bind.bind,Pure.pure]
 apply leaves_bind
 rintro ⟨r,after⟩
 cases r <;> simp only [AllLeaves,FramePost,advance,rank,nextOrError]
#print axioms frame_prepare
theorem progress_prepare (cfg : Configuration) (i : Input) (g : Scratch) :
 AllLeaves (ProgressPost ⟨i,.prepare g⟩) (step cfg ⟨i,.prepare g⟩) := by
 dsimp only [step]
 simp only [Bind.bind,Pure.pure]
 apply leaves_bind
 rintro ⟨r,after⟩
 cases r <;> simp only [AllLeaves,ProgressPost,advance,rank,nextOrError]
#print axioms progress_prepare
theorem frame_accumulator (cfg : Configuration) (i : Input) (g : Scratch) (p : verifier.Prepared) :
 AllLeaves (FramePost ⟨i,.accumulator g p⟩) (step cfg ⟨i,.accumulator g p⟩) := by
 dsimp only [step]
 simp only [Bind.bind,Pure.pure]
 repeat' first
 | (apply leaves_bind; intro reply; cases reply)
 | (split)
 | (simp only [AllLeaves,FramePost,advance,rank,nextOrError])
 | trivial
 | decide
#print axioms frame_accumulator
theorem progress_accumulator (cfg : Configuration) (i : Input) (g : Scratch) (p : verifier.Prepared) :
 AllLeaves (ProgressPost ⟨i,.accumulator g p⟩) (step cfg ⟨i,.accumulator g p⟩) := by
 dsimp only [step]
 simp only [Bind.bind,Pure.pure]
 repeat' first
 | (apply leaves_bind; intro reply; cases reply)
 | (split)
 | (simp only [AllLeaves,ProgressPost,advance,rank,nextOrError])
 | trivial
 | decide
#print axioms progress_accumulator
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
theorem frame_foldedSlice (cfg : Configuration) (i : Input) (g : Scratch) (p : verifier.Prepared) (a : verifier.Accumulator) :
 AllLeaves (FramePost ⟨i,.foldedSlice g p a⟩) (step cfg ⟨i,.foldedSlice g p a⟩) := by
 dsimp only [step]
 simp only [Bind.bind,Pure.pure]
 repeat' first
 | (apply leaves_bind; intro reply; cases reply)
 | (split)
 | (simp only [AllLeaves,FramePost,advance,rank,nextOrError])
 | trivial
 | decide
#print axioms frame_foldedSlice
theorem progress_foldedSlice (cfg : Configuration) (i : Input) (g : Scratch) (p : verifier.Prepared) (a : verifier.Accumulator) :
 AllLeaves (ProgressPost ⟨i,.foldedSlice g p a⟩) (step cfg ⟨i,.foldedSlice g p a⟩) := by
 dsimp only [step]
 simp only [Bind.bind,Pure.pure]
 repeat' first
 | (apply leaves_bind; intro reply; cases reply)
 | (split)
 | (simp only [AllLeaves,ProgressPost,advance,rank,nextOrError])
 | trivial
 | decide
#print axioms progress_foldedSlice
theorem frame_foldedCopy (cfg : Configuration) (i : Input) (g : Scratch) (p : verifier.Prepared) (a : verifier.Accumulator) (slice : Slice U8) :
 AllLeaves (FramePost ⟨i,.foldedCopy g p a slice⟩) (step cfg ⟨i,.foldedCopy g p a slice⟩) := by
 dsimp only [step]
 simp only [Bind.bind,Pure.pure]
 repeat' first
 | (apply leaves_bind; intro reply; cases reply)
 | (split)
 | (simp only [AllLeaves,FramePost,advance,rank,nextOrError])
 | trivial
 | decide
#print axioms frame_foldedCopy
theorem progress_foldedCopy (cfg : Configuration) (i : Input) (g : Scratch) (p : verifier.Prepared) (a : verifier.Accumulator) (slice : Slice U8) :
 AllLeaves (ProgressPost ⟨i,.foldedCopy g p a slice⟩) (step cfg ⟨i,.foldedCopy g p a slice⟩) := by
 dsimp only [step]
 simp only [Bind.bind,Pure.pure]
 repeat' first
 | (apply leaves_bind; intro reply; cases reply)
 | (split)
 | (simp only [AllLeaves,ProgressPost,advance,rank,nextOrError])
 | trivial
 | decide
#print axioms progress_foldedCopy
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
theorem frame_batch0 (cfg : Configuration) (i : Input) (g : Scratch) (p : verifier.Prepared) (a : verifier.Accumulator) (root : Root) :
 AllLeaves (FramePost ⟨i,.batch0 g p a root⟩) (step cfg ⟨i,.batch0 g p a root⟩) := by
 dsimp only [step]
 simp only [Bind.bind,Pure.pure]
 repeat' first
 | (apply leaves_bind; intro reply; cases reply)
 | (split)
 | (simp only [AllLeaves,FramePost,advance,rank,nextOrError])
 | trivial
 | decide
#print axioms frame_batch0
theorem progress_batch0 (cfg : Configuration) (i : Input) (g : Scratch) (p : verifier.Prepared) (a : verifier.Accumulator) (root : Root) :
 AllLeaves (ProgressPost ⟨i,.batch0 g p a root⟩) (step cfg ⟨i,.batch0 g p a root⟩) := by
 dsimp only [step]
 simp only [Bind.bind,Pure.pure]
 repeat' first
 | (apply leaves_bind; intro reply; cases reply)
 | (split)
 | (simp only [AllLeaves,ProgressPost,advance,rank,nextOrError])
 | trivial
 | decide
#print axioms progress_batch0
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
theorem frame_geometry (cfg : Configuration) (i : Input) (g : Scratch) (p : verifier.Prepared) (a : verifier.Accumulator) :
 AllLeaves (FramePost ⟨i,.geometry g p a⟩) (step cfg ⟨i,.geometry g p a⟩) := by
 dsimp only [step]
 simp only [Bind.bind,Pure.pure]
 repeat' first
 | (apply leaves_bind; intro reply; cases reply)
 | (split)
 | (simp only [AllLeaves,FramePost,advance,rank,nextOrError])
 | trivial
 | decide
#print axioms frame_geometry
theorem progress_geometry (cfg : Configuration) (i : Input) (g : Scratch) (p : verifier.Prepared) (a : verifier.Accumulator) :
 AllLeaves (ProgressPost ⟨i,.geometry g p a⟩) (step cfg ⟨i,.geometry g p a⟩) := by
 dsimp only [step]
 simp only [Bind.bind,Pure.pure]
 repeat' first
 | (apply leaves_bind; intro reply; cases reply)
 | (split)
 | (simp only [AllLeaves,ProgressPost,advance,rank,nextOrError])
 | trivial
 | decide
#print axioms progress_geometry
theorem frame_pending (cfg : Configuration) (i : Input) (g : Scratch) (p : verifier.Prepared) (a : verifier.Accumulator) (geom : verifier.QueryGeometry) :
 AllLeaves (FramePost ⟨i,.pending g p a geom⟩) (step cfg ⟨i,.pending g p a geom⟩) := by
 dsimp only [step]
 simp only [Bind.bind,Pure.pure]
 repeat' first
 | (apply leaves_bind; intro reply; cases reply)
 | (split)
 | (simp only [AllLeaves,FramePost,advance,rank,nextOrError])
 | trivial
 | decide
#print axioms frame_pending
theorem progress_pending (cfg : Configuration) (i : Input) (g : Scratch) (p : verifier.Prepared) (a : verifier.Accumulator) (geom : verifier.QueryGeometry) :
 AllLeaves (ProgressPost ⟨i,.pending g p a geom⟩) (step cfg ⟨i,.pending g p a geom⟩) := by
 dsimp only [step]
 simp only [Bind.bind,Pure.pure]
 repeat' first
 | (apply leaves_bind; intro reply; cases reply)
 | (split)
 | (simp only [AllLeaves,ProgressPost,advance,rank,nextOrError])
 | trivial
 | decide
#print axioms progress_pending
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
theorem frame_checkpoint (cfg : Configuration) (i : Input) (p : verifier.Prepared) (a : verifier.Accumulator) :
 AllLeaves (FramePost ⟨i,.checkpoint p a⟩) (step cfg ⟨i,.checkpoint p a⟩) := by
 dsimp only [step]
 simp only [Bind.bind,Pure.pure]
 repeat' first
 | (apply leaves_bind; intro reply; cases reply)
 | (split)
 | (simp only [AllLeaves,FramePost,advance,rank,nextOrError])
 | trivial
 | decide
#print axioms frame_checkpoint
theorem progress_checkpoint (cfg : Configuration) (i : Input) (p : verifier.Prepared) (a : verifier.Accumulator) :
 AllLeaves (ProgressPost ⟨i,.checkpoint p a⟩) (step cfg ⟨i,.checkpoint p a⟩) := by
 dsimp only [step]
 simp only [Bind.bind,Pure.pure]
 repeat' first
 | (apply leaves_bind; intro reply; cases reply)
 | (split)
 | (simp only [AllLeaves,ProgressPost,advance,rank,nextOrError])
 | trivial
 | decide
#print axioms progress_checkpoint
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
