import RWireRawCutLiteralRowZeroOrder
import RWireRawCutLiteralReseedOrder
import RWireRawCutLiteralQueryAdjacent
import RWireRawCutLiteralNextFrame
import RWireRawCutLiteralSamplerOrder
import RawCutLiteralStateSuccessor
import RawCutLiteralInitialAdvanceRead

set_option autoImplicit false
noncomputable section
namespace AspisR1.RWireRawCutLiteralAllFrames

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1.LiteralTranscript
open AspisR1.RawCutWordsFromView
open AspisR1.RawCutProverCompiler
open AspisR1.BinRawByteCollisionTargets

/-- Adjacent literal frames occur in transcript order throughout the actual
33-row verifier execution, under the stated raw all-address no-hit event. -/
theorem all_adjacent_frame_order
    (decoder : LiteralByteProtocol.Decoder)
    (d : RawCutTranscriptRun.ErasedPrefix → RawCutTranscriptRun.ErasedMessage → Bool)
    (prover : Prover) (H : Bytes → State) (run : RawCutProverCompiler.RunView)
    (hrun : run = eval H (experiment prover (verifier decoder d)))
    (iv : State) (Q : Nat)
    (hQ : firstReads emptyTable run.1 ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q)
      emptyTable run.1)
    (hvalid : ∀ i, i < 33 → LiteralTranscript.valid i (run.2.1.2 i)) :
    ∀ i, i < 32 →
      Before run.1
        (RawCutWordsFromView.frame decoder H run.2.1.1 run.2.1.2 i)
        (RawCutWordsFromView.frame decoder H run.2.1.1 run.2.1.2 (i + 1)) := by
  intro i hi
  by_cases h0 : i = 0
  · subst i
    have hv0 := hvalid 0 (by decide)
    obtain ⟨c1, word, hmsg, hreadAdv⟩ :=
      RawCutLiteralInitialAdvanceRead.initial_advance_read decoder d prover H run hrun hv0
    have hzero := RWireRawCutLiteralRowZeroOrder.row_zero_frame_before_advance
      decoder d prover H run hrun iv Q hQ hout hv0
    have hzero' : Before run.1
        (RawCutWordsFromView.frame decoder H run.2.1.1 run.2.1.2 0)
        (advanceA SelectedTranscriptParams.params
          (H (PublicInitFrame.row0 SelectedTranscriptParams.params
            (by norm_num [SelectedTranscriptParams.params, SelectedTranscriptParams.D])
            (H (PublicInitFrame.addr run.2.1.1.pubBytes
              run.2.1.1.initFits c1).toBytes)).toBytes)).toBytes := by
      simpa only [hmsg] using hzero
    let P := (LiteralByteProtocol.protocol decoder).transcript H run.2.1.1 run.2.1.2 0
    let p := SelectedTranscriptParams.params
    have hD : 5 ≤ p.D := by norm_num [p, SelectedTranscriptParams.params, SelectedTranscriptParams.D]
    have hsucc := RawCutLiteralTranscriptSuccessor.actual_successor_state decoder H
      run.2.1.1 run.2.1.2 0
    have hchain : (LiteralByteProtocol.protocol decoder).chain H run.2.1.1 run.2.1.2 0 =
        LiteralByteSampler.samp 0 P (run.2.1.2 0) := rfl
    rw [hchain, hmsg] at hsucc
    have hsample : (eval H (LiteralByteSampler.samp 0 P (.initial c1 word)).toProgram).2.2 =
        H ((advanceA p (H (PublicInitFrame.row0 p hD
          (H (PublicInitFrame.addr P.statement.pubBytes P.statement.initFits c1).toBytes)).toBytes)).toBytes) := by
      rw [LiteralByteSampler.eval_eq]
      simp only [AspisV8R19.OracleProgramOps.mapView]
      change (eval (fun a : FS2.Duplex.Addr SelectedTranscriptParams.L => H a.toBytes)
        (LiteralTranscript.samp 0 P (.initial c1 word)).toProgram).2.2 = _
      change (eval (fun a : FS2.Duplex.Addr SelectedTranscriptParams.L => H a.toBytes)
        (UnifiedSampler.samp p hD 0 (LiteralTranscript.erasePrefix P) (.initial c1)).toProgram).2.2 = _
      rw [UnifiedSampler.row_zero p hD (LiteralTranscript.erasePrefix P) c1]
      rw [DuplexSamplers.initial_eval]
      rfl
    have hstate : UnifiedSampler.stateOf p
        (LiteralTranscript.erasePrefix
          ((LiteralByteProtocol.protocol decoder).transcript H run.2.1.1 run.2.1.2 1)) =
        H ((advanceA p (H (PublicInitFrame.row0 p hD
          (H (PublicInitFrame.addr P.statement.pubBytes P.statement.initFits c1).toBytes)).toBytes)).toBytes) := by
      exact hsucc.trans hsample
    have hnext := RWireRawCutLiteralNextFrame.state_address_before_next_frame
      decoder d prover H run hrun iv Q hQ hout (j := 1) (by decide) (by decide)
      (hvalid 1 (by decide))
      (advanceA SelectedTranscriptParams.params
        (H (PublicInitFrame.row0 SelectedTranscriptParams.params
          (by norm_num [SelectedTranscriptParams.params, SelectedTranscriptParams.D])
          (H (PublicInitFrame.addr run.2.1.1.pubBytes
            run.2.1.1.initFits c1).toBytes)).toBytes)) hstate hreadAdv
    exact before_trans run.1 hzero' hnext
  · by_cases h26 : i = 26
    · subst i
      exact RWireRawCutLiteralReseedOrder.row26_frame_before_row27 decoder d prover H run hrun iv Q hQ hout
        (hvalid 26 (by decide)) (hvalid 27 (by decide))
    · by_cases h31 : i = 31
      · subst i
        exact RWireRawCutLiteralQueryAdjacent.row31_frame_before_row32 decoder d prover H run hrun iv Q hQ hout
          (hvalid 31 (by decide)) (hvalid 32 (by decide))
      · have hi0 : i ≠ 0 := h0
        have hi26 : i ≠ 26 := h26
        have hi31 : i ≠ 31 := h31
        have hprev := RWireRawCutLiteralSamplerOrder.ordinary_frame_before_advance
          decoder d prover H run hrun iv Q hQ hout (by omega) hi0 (hvalid i (by omega))
        have hstate := RWireRawCutLiteralNextFrame.ordinary_next_prefix_state
          decoder H run.2.1.1 run.2.1.2 hi0 hi26 hi31 (hvalid i (by omega))
        have hread := RWireRawCutLiteralNextFrame.ordinary_advance_read
          decoder d prover H run hrun (by omega) hi0 hi26 hi31 (hvalid i (by omega))
        exact RWireRawCutLiteralNextFrame.adjacent_frame_order_of_sampler_state
          decoder d prover H run hrun iv Q hQ hout (by omega)
          (hvalid i (by omega)) (hvalid (i + 1) (by omega))
          (advanceA SelectedTranscriptParams.params
            (H (RawCutWordsFromView.frame decoder H run.2.1.1 run.2.1.2 i)))
          hprev hstate hread

#print axioms all_adjacent_frame_order


end AspisR1.RWireRawCutLiteralAllFrames
end
