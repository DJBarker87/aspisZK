import RawCommitmentFrameReplay
import RawCutCommitmentFrames

/-! State-only recorded replay agrees with the literal byte protocol before
its query row. Only valid constructor scheduling is assumed; no recovered-word
or commitment-frame equality is supplied as a premise. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawCommitmentFrameReplayCorrect
open FS FS2 FS2.Duplex
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open RawCommitmentFrameReplay

private theorem transcript_statement (decoder : LiteralByteProtocol.Decoder)
    (H : Bytes → State) (pub : Public) (pf : Proof) : ∀ n,
    ((LiteralByteProtocol.protocol decoder).transcript H pub pf n).statement = pub := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => exact ih

/-- The raw replay stores precisely the prefix state at every position up to
31. The special public initialization and row-26 reseed are included. -/
theorem stateBefore_eq (decoder : LiteralByteProtocol.Decoder)
    (H : Bytes → State) (pub : Public) (pf : Proof) : ∀ n,
    n ≤ 31 → (∀ j, j < n → LiteralTranscript.valid j (pf j)) →
    RawCommitmentFrameReplay.stateBefore H pub pf n =
      UnifiedSampler.stateOf SelectedTranscriptParams.params
        (LiteralTranscript.erasePrefix
          ((LiteralByteProtocol.protocol decoder).transcript H pub pf n)) := by
  intro n
  induction n with
  | zero => intro _ _; rfl
  | succ n ih =>
    intro hn hvalid
    rw [RawCommitmentFrameReplay.stateBefore,
      ih (by omega) (fun j hj => hvalid j (by omega))]
    rw [RawCutLiteralTranscriptSuccessor.actual_successor_state decoder H pub pf n]
    exact RawCommitmentFrameReplay.successor_eq_sampler H pub
      ((LiteralByteProtocol.protocol decoder).transcript H pub pf n)
      (transcript_statement decoder H pub pf n) n (by omega) (pf n)
      (hvalid n (by omega))

theorem frame_zero_eq (decoder : LiteralByteProtocol.Decoder)
    (H : Bytes → State) (pub : Public) (pf : Proof)
    (root : State) (word : LiteralTranscript.C1Word)
    (hm : pf 0 = .initial root word) :
    RawCommitmentFrameReplay.frame H pub pf 0 =
      RawCutWordsFromView.frame decoder H pub pf 0 := by
  unfold RawCommitmentFrameReplay.frame RawCutWordsFromView.frame
  change RawCommitmentFrameReplay.frameAt pub _ 0 (pf 0) =
    (firstCell (LiteralByteSampler.samp 0
      ((LiteralByteProtocol.protocol decoder).transcript H pub pf 0) (pf 0))).getD []
  rw [hm, RawCutCommitmentFrames.first_initial]
  simp only [RawCommitmentFrameReplay.frameAt, Option.getD_some]
  rw [transcript_statement decoder H pub pf 0]
  have h := RawTranscriptFrameBytes.publicInit_eq pub.pubBytes pub.initFits root
  rw [PublicInitFrame.addr, Addr.toBytes_ofBytes] at h
  exact h

theorem frame_two_eq (decoder : LiteralByteProtocol.Decoder)
    (H : Bytes → State) (pub : Public) (pf : Proof)
    (payload : LiteralTranscript.BytesMessage) (word : LiteralTranscript.C2Word)
    (hm : pf 2 = .c2 payload word)
    (hvalid : ∀ j, j < 2 → LiteralTranscript.valid j (pf j)) :
    RawCommitmentFrameReplay.frame H pub pf 2 =
      RawCutWordsFromView.frame decoder H pub pf 2 := by
  unfold RawCommitmentFrameReplay.frame RawCutWordsFromView.frame
  change RawCommitmentFrameReplay.frameAt pub _ 2 (pf 2) =
    (firstCell (LiteralByteSampler.samp 2
      ((LiteralByteProtocol.protocol decoder).transcript H pub pf 2) (pf 2))).getD []
  rw [hm, RawCutCommitmentFrames.first_c2]
  simp only [RawCommitmentFrameReplay.frameAt, Option.getD_some]
  rw [stateBefore_eq decoder H pub pf 2 (by omega) hvalid]
  rfl

theorem frame_thirty_eq (decoder : LiteralByteProtocol.Decoder)
    (H : Bytes → State) (pub : Public) (pf : Proof)
    (payload : LiteralTranscript.BytesMessage) (word : LiteralTranscript.VWord)
    (hm : pf 30 = .second payload word)
    (hvalid : ∀ j, j < 30 → LiteralTranscript.valid j (pf j)) :
    RawCommitmentFrameReplay.frame H pub pf 30 =
      RawCutWordsFromView.frame decoder H pub pf 30 := by
  unfold RawCommitmentFrameReplay.frame RawCutWordsFromView.frame
  change RawCommitmentFrameReplay.frameAt pub _ 30 (pf 30) =
    (firstCell (LiteralByteSampler.samp 30
      ((LiteralByteProtocol.protocol decoder).transcript H pub pf 30) (pf 30))).getD []
  rw [hm, RawCutCommitmentFrames.first_second]
  simp only [RawCommitmentFrameReplay.frameAt, Option.getD_some]
  rw [stateBefore_eq decoder H pub pf 30 (by omega) hvalid]
  rfl

/-- Compatibility at exactly the three cuts used by word recovery. -/
theorem commitment_frames_eq (decoder : LiteralByteProtocol.Decoder)
    (H : Bytes → State) (pub : Public) (pf : Proof)
    (hvalid : ∀ j, j ≤ 30 → LiteralTranscript.valid j (pf j)) :
    RawCommitmentFrameReplay.frame H pub pf 0 = RawCutWordsFromView.frame decoder H pub pf 0 ∧
    RawCommitmentFrameReplay.frame H pub pf 2 = RawCutWordsFromView.frame decoder H pub pf 2 ∧
    RawCommitmentFrameReplay.frame H pub pf 30 = RawCutWordsFromView.frame decoder H pub pf 30 := by
  have h0 : ∃ root word, pf 0 = .initial root word := by
    have hv := hvalid 0 (by omega)
    cases hm : pf 0 with
    | initial root word => exact ⟨root, word, rfl⟩
    | payload p => simp [hm, LiteralTranscript.valid] at hv
    | c2 p w => simp [hm, LiteralTranscript.valid] at hv
    | second p w => simp [hm, LiteralTranscript.valid] at hv
  have h2 : ∃ payload word, pf 2 = .c2 payload word := by
    have hv := hvalid 2 (by omega)
    cases hm : pf 2 with
    | initial r w => simp [hm, LiteralTranscript.valid] at hv
    | payload p => simp [hm, LiteralTranscript.valid] at hv
    | c2 p w => exact ⟨p, w, rfl⟩
    | second p w => simp [hm, LiteralTranscript.valid] at hv
  have h30 : ∃ payload word, pf 30 = .second payload word := by
    have hv := hvalid 30 (by omega)
    cases hm : pf 30 with
    | initial r w => simp [hm, LiteralTranscript.valid] at hv
    | payload p => simp [hm, LiteralTranscript.valid] at hv
    | c2 p w => simp [hm, LiteralTranscript.valid] at hv
    | second p w => exact ⟨p, w, rfl⟩
  obtain ⟨r, w1, hr⟩ := h0
  obtain ⟨p2, w2, hp2⟩ := h2
  obtain ⟨p30, w30, hp30⟩ := h30
  exact ⟨frame_zero_eq decoder H pub pf r w1 hr,
    frame_two_eq decoder H pub pf p2 w2 hp2 (fun j hj => hvalid j (by omega)),
    frame_thirty_eq decoder H pub pf p30 w30 hp30 (fun j hj => hvalid j (by omega))⟩

/-- The recorded-view caller gets these frame equalities from valid rows,
without assuming a separate frame-compatibility contract. -/
theorem frameFromView_commitments_eq (decoder : LiteralByteProtocol.Decoder)
    (run : RawCutProverCompiler.RunView)
    (hvalid : ∀ j, j ≤ 30 → LiteralTranscript.valid j (run.2.1.2 j)) :
    RawCommitmentFrameReplay.frameFromView run 0 = RawCutWordsFromView.frameFromView decoder run 0 ∧
    RawCommitmentFrameReplay.frameFromView run 2 = RawCutWordsFromView.frameFromView decoder run 2 ∧
    RawCommitmentFrameReplay.frameFromView run 30 = RawCutWordsFromView.frameFromView decoder run 30 := by
  exact commitment_frames_eq decoder (OracleProgramReplay.oracleOf run.1)
    run.2.1.1 run.2.1.2 hvalid

#print axioms stateBefore_eq
#print axioms frame_zero_eq
#print axioms frame_two_eq
#print axioms frame_thirty_eq
#print axioms commitment_frames_eq
#print axioms frameFromView_commitments_eq
end AspisR1.RawCommitmentFrameReplayCorrect
end
