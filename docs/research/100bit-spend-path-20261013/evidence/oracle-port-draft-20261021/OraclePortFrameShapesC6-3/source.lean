import OraclePortReachedRunC6

set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortFrameShapesC6
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

theorem firstCell_map {I J A C : Type} [DecidableEq I] [Inhabited A]
    (f : I → J) (s : Sampler I A C) :
    firstCell (ProgramSamplerMap.map f s) = (firstCell s).map f := by
  cases s <;> rfl

theorem initial (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (pub : LiteralTranscript.Public) (pf : LiteralProtocol.Proof) (root : State)
    (message : LiteralTranscript.erase (pf 0) = .initial root) :
    RawCutWordsFromView.frame D H pub pf 0 = PublicInitFrame.frame pub.pubBytes root := by
  unfold RawCutWordsFromView.frame
  change (firstCell (ProgramSamplerMap.map Addr.toBytes
    (LiteralTranscript.samp 0 ((LiteralByteProtocol.protocol D).transcript H pub pf 0) (pf 0)))).getD [] = _
  rw [firstCell_map]
  unfold LiteralTranscript.samp
  rw [message,UnifiedSampler.row_zero]
  simp only [DuplexSamplers.initial,firstCell,Option.map_some,Option.getD_some,PublicInitFrame.addr_bytes]
  rfl

theorem ordinary (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (pub : LiteralTranscript.Public) (pf : LiteralProtocol.Proof) (row : Nat)
    (h0 : row ≠ 0) (h26 : row ≠ 26) (h31 : row ≠ 31)
    (b : LiteralTranscript.BytesMessage) (message : LiteralTranscript.erase (pf row) = .payload b) :
    RawCutWordsFromView.frame D H pub pf row =
      (UnifiedSampler.absorb SelectedTranscriptParams.params row
        (LiteralTranscript.erasePrefix ((LiteralByteProtocol.protocol D).transcript H pub pf row)) b).toBytes := by
  unfold RawCutWordsFromView.frame
  change (firstCell (ProgramSamplerMap.map Addr.toBytes
    (LiteralTranscript.samp row ((LiteralByteProtocol.protocol D).transcript H pub pf row) (pf row)))).getD [] = _
  rw [firstCell_map]
  unfold LiteralTranscript.samp
  rw [message,UnifiedSampler.row_ordinary _ _ row h0 h26 h31]
  rfl

#print FS2.Duplex.absorbA
#print FS2.Duplex.Addr.toBytes

theorem absorb_bytes (row : Nat) (P : LiteralTranscript.Prefix) (b : LiteralTranscript.BytesMessage) :
    (UnifiedSampler.absorb SelectedTranscriptParams.params row (LiteralTranscript.erasePrefix P) b).toBytes =
      bytes (UnifiedSampler.stateOf SelectedTranscriptParams.params (LiteralTranscript.erasePrefix P)) ++
        [0,SelectedTranscriptParams.label row] ++ b.val := rfl

theorem initial_target (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (pub : LiteralTranscript.Public) (pf : LiteralProtocol.Proof) (root : State)
    (message : LiteralTranscript.erase (pf 0) = .initial root) :
    BinRawByteCollisionTargets.pred 2 (RawCutWordsFromView.frame D H pub pf 0) = some root := by
  rw [initial D H pub pf root message,BinRawByteCollisionTargets.pred_tail]
  exact BinRawByteCollisionTargets.trailing_frame (PublicInitFrame.pre pub.pubBytes) root

#print axioms firstCell_map
#print axioms initial
#print axioms ordinary
#print axioms absorb_bytes
#print axioms initial_target
end AspisR1.OraclePortFrameShapesC6
end
