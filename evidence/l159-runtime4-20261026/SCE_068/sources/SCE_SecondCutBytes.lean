import SCE_SecondIndex
import SCE_SnapshotRead
import S2W_NativeConsolidation
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCE_SecondCutBytes
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_NativeConsolidation
open MultiproofConeCanonical

/-- Source-selected TX2 checkpoint bytes are the actual response-selected
entry buffer. No different checkpoint or future allocation is substituted. -/
theorem checkpoint (e : Entry) (ops : AdapterRw.Ops)
    (accounts1 : S2W_ExtractionBoundary.Accounts) (saved : alloc.vec.Vec U8)
    (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts ops accounts1 (e.second S2W_D189Wrappers.secondSizes) saved f s) :
    bytesOf s.checkpoint.val = bytesOf (e.buffers (e.handles 6).1).val := by
  have index := Result.ok.inj ((SCE_SecondIndex.checkpoint6 e _).symm.trans cuts.checkpoint2Index)
  have read := cuts.checkpoint2Read
  rw [← index] at read
  exact congrArg bytesOf (SCE_SnapshotRead.buffer e ops 6 _ _ s.checkpoint read).1

theorem raw_proof (e : Entry) (ops : AdapterRw.Ops)
    (accounts1 : S2W_ExtractionBoundary.Accounts) (saved : alloc.vec.Vec U8)
    (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts ops accounts1 (e.second S2W_D189Wrappers.secondSizes) saved f s) :
    bytesOf s.raw.val = bytesOf (e.buffers (e.handles 0).1).val := by
  have index := Result.ok.inj ((SCE_SecondIndex.proof0 e _).symm.trans cuts.proof2Index)
  have read := cuts.proof2Read
  rw [← index] at read
  exact congrArg bytesOf (SCE_SnapshotRead.buffer e ops 0 _ _ s.raw read).1

#print axioms checkpoint
#print axioms raw_proof
end AspisR1.SCE_SecondCutBytes
end
