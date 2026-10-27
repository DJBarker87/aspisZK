import Hist_ArgumentCuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hist_InputUniqueness
open Aeneas Aeneas.Std Result S2W_NativeConsolidation
open MultiproofConeCanonical AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem first_bytes (ops : AdapterRw.Ops) (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts)
    (saved : alloc.vec.Vec U8) (f g : FirstCut) (s t : SecondCut)
    (left : SourceCuts ops accounts1 accounts2 saved f s)
    (right : SourceCuts ops accounts1 accounts2 saved g t) :
    bytesOf g.proof.val = bytesOf f.proof.val ∧ bytesOf g.pub.val = bytesOf f.pub.val := by
  have sameProofAccount := Result.ok.inj (left.proof1Index.symm.trans right.proof1Index)
  have readProof := left.proof1Read
  rw [sameProofAccount] at readProof
  have sameRaw := core.result.Result.Ok.inj (Result.ok.inj (readProof.symm.trans right.proof1Read))
  have suffix := right.firstSuffix
  rw [← sameRaw] at suffix
  have proof := List.append_cancel_left (left.firstSuffix.symm.trans suffix)
  have samePublicAccount := Result.ok.inj (left.public1Index.symm.trans right.public1Index)
  have readPub := left.public1Read
  rw [samePublicAccount] at readPub
  have pub := core.result.Result.Ok.inj (Result.ok.inj (readPub.symm.trans right.public1Read))
  exact ⟨proof.symm,congrArg (fun x : Slice U8 => bytesOf x.val) pub.symm⟩

theorem second_proof_checkpoint (ops : AdapterRw.Ops) (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts)
    (saved : alloc.vec.Vec U8) (f g : FirstCut) (s t : SecondCut)
    (left : SourceCuts ops accounts1 accounts2 saved f s)
    (right : SourceCuts ops accounts1 accounts2 saved g t) :
    bytesOf t.proof.val = bytesOf s.proof.val ∧ bytesOf t.checkpoint.val = bytesOf s.checkpoint.val := by
  have sameProofAccount := Result.ok.inj (left.proof2Index.symm.trans right.proof2Index)
  have readProof := left.proof2Read
  rw [sameProofAccount] at readProof
  have sameRaw := core.result.Result.Ok.inj (Result.ok.inj (readProof.symm.trans right.proof2Read))
  have suffix := right.secondSuffix
  rw [← sameRaw] at suffix
  have proof := List.append_cancel_left (left.secondSuffix.symm.trans suffix)
  have sameCheckpointAccount := Result.ok.inj (left.checkpoint2Index.symm.trans right.checkpoint2Index)
  have readCheckpoint := left.checkpoint2Read
  rw [sameCheckpointAccount] at readCheckpoint
  have checkpoint := core.result.Result.Ok.inj (Result.ok.inj (readCheckpoint.symm.trans right.checkpoint2Read))
  exact ⟨proof.symm,congrArg (fun x : Slice U8 => bytesOf x.val) checkpoint.symm⟩

/-- Unlike the old SourceCuts projection, the actual validation AND encoder
returns uniquely identify TX2's reconstructed1880-byte public value. -/
theorem second_public (ops : AdapterRw.Ops) (program : S2W_ExtractionBoundary.Program)
    (accounts : S2W_ExtractionBoundary.Accounts) (data : Slice U8) (slot : S2W_ExtractionBoundary.Slot)
    (s t : SecondCut) (v w : AdapterRw.r1_pool_adapter.ValidatedAsqa)
    (left : AdapterRw.r1_pool_adapter.owned.validate_asq8 ops program accounts data slot = ok (.Ok v))
    (right : AdapterRw.r1_pool_adapter.owned.validate_asq8 ops program accounts data slot = ok (.Ok w))
    (encodedLeft : ops.op22 v.statement = ok (.Ok s.encoded))
    (encodedRight : ops.op22 w.statement = ok (.Ok t.encoded)) :
    bytesOf t.pub.val = bytesOf s.pub.val := by
  have same := core.result.Result.Ok.inj (Result.ok.inj (left.symm.trans right))
  subst w
  have encoded := core.result.Result.Ok.inj (Result.ok.inj (encodedLeft.symm.trans encodedRight))
  exact congrArg (fun x : Array U8 1880#usize => bytesOf x.val) encoded.symm

#print axioms first_bytes
#print axioms second_proof_checkpoint
#print axioms second_public
end AspisR1.Hist_InputUniqueness
end
