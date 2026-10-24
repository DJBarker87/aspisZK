import Port6AUTH_Compiler
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port6AUTH_WordStability
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open OraclePortStoredExperimentC4 OraclePortStoredAdmissionC4 OraclePortRuntimeBindingC7
open Port1_StoredCarrier Port6AUTH_Prefix Port6AUTH_SourceCut
attribute [local irreducible] originalWith canon lift source LiteralByteProtocol.protocol

/-- Realized sampler-read agreement suffices to reconstruct a frame from any
consistent containing source log. No source/model execution identity. -/
theorem frame_replay (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (pub : LiteralTranscript.Public) (pf : LiteralProtocol.Proof) (log : List (Bytes × State))
    (consistent : ∀ a ∈ log, a.2=H a.1)
    (contains : ∀ a, Read (eval H (RawCutProverCompiler.verifier D (fun _ _ => false) pub pf)).1 a → Read log a)
    (row : Nat) (bound : row≤33) :
    RawCutWordsFromView.frame D (OracleProgramReplay.oracleOf log) pub pf row=
      RawCutWordsFromView.frame D H pub pf row := by
  unfold RawCutWordsFromView.frame FS2.Protocol.chain
  have transcript := OracleProgramReplay.transcript_eq_of_agrees (LiteralByteProtocol.protocol D)
    (RawCutTranscriptRun.decisionOnBytes (fun _ _ => false)) H (OracleProgramReplay.oracleOf log) pub pf
    (fun a ha => OracleProgramReplay.oracleOf_eq H log consistent a (contains a ha)) row
    (by simpa only [LiteralByteProtocol.protocol] using bound)
  rw [transcript]

/-- Both annotation passes preserve the literal first-commitment cuts and the
entire binary word builder on the actual source record, even on rejection.
The source may have different terminal behavior from the frozen model. -/
theorem words_stable (D : LiteralByteProtocol.Decoder) (rust : Verifier) (P : ByteProver) (H : Bytes → State)
    (contains : ∀ a, Read (eval H (RawCutProverCompiler.verifier D (fun _ _ => false)
      (first rust P H).2.1.statement (first rust P H).2.1.proof)).1 a → Read (first rust P H).1 a) :
    build D (eval H (source D rust P))=build D (view (first rust P H)) := by
  let before := view (first rust P H)
  let after := eval H (source D rust P)
  have hp : after.2.1.1=before.2.1.1 := by
    simp only [after,before,source_eval,OraclePortFrozen2Join.annotatedWith_eval,view]
  have hf : after.2.1.2=RawCutTranscriptRun.proof (build D before) before.2.1.2 := by
    simp only [after,before,source_eval,OraclePortFrozen2Join.annotatedWith_eval,view,enrich]
  obtain ⟨tail,append⟩ := first_pass_prefix D rust P H
  have containsAfter : ∀ a, Read (eval H (RawCutProverCompiler.verifier D (fun _ _ => false)
      before.2.1.1 before.2.1.2)).1 a → Read after.1 a := by
    intro a ha
    change Read (eval H (source D rust P)).1 a
    rw [append]
    simp only [Read,List.map_append,List.mem_append]
    exact Or.inl (contains a ha)
  have frameSame (row : Nat) (bound : row<33) :
      RawCutWordsFromView.frameFromView D after row=RawCutWordsFromView.frameFromView D before row := by
    unfold RawCutWordsFromView.frameFromView
    rw [hp,hf]
    have erase := congrArg (fun chain => (firstCell chain).getD [])
      (RawCutTranscriptRun.chain_eq D (build D before) (OracleProgramReplay.oracleOf after.1)
        before.2.1.1 before.2.1.2 row)
    change RawCutWordsFromView.frame D (OracleProgramReplay.oracleOf after.1) before.2.1.1
      (RawCutTranscriptRun.proof (build D before) before.2.1.2) row=
      RawCutWordsFromView.frame D (OracleProgramReplay.oracleOf before.1) before.2.1.1 before.2.1.2 row
    rw [erase,frame_replay D H before.2.1.1 before.2.1.2 after.1
      (FS.eval_consistent H (source D rust P)) containsAfter row (by omega)]
    exact (frame_eq D rust P H contains row (by omega)).symm
  have cuts (row : Nat) (bound : row<33) :
      BinRawByteCutRecovery.cut after.1 (RawCutWordsFromView.frameFromView D before row)=
        BinRawByteCutRecovery.cut before.1 (RawCutWordsFromView.frameFromView D before row) := by
    have read : Read before.1 (RawCutWordsFromView.frameFromView D before row) := by
      rw [frame_eq D rust P H contains row (by omega)]
      exact contains _ (OraclePortReplay.frame_in_sampler D H _ _ row bound)
    change BinRawByteCutRecovery.cut (eval H (source D rust P)).1 _=_
    rw [append]
    exact OracleProgramRecording.cut_append_of_read _ _ _ read
  change build D after=build D before
  unfold build BinCompiledRunWordStability.wordsFromRun
  rw [frameSame 0 (by decide),frameSame 2 (by decide),frameSame 30 (by decide)]
  unfold BinCanonicalCutWords.wordsFromRawCuts BinCanonicalCutWords.rawC1Map
    BinCanonicalCutWords.rawC2Map BinCanonicalCutWords.rawFoldedMap
  dsimp only
  rw [cuts 0 (by decide),cuts 2 (by decide),cuts 30 (by decide)]

#print axioms frame_replay
#print axioms words_stable
end AspisR1.Port6AUTH_WordStability
end
