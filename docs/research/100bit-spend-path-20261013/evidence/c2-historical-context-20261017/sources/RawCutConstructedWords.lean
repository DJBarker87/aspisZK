import RawCutCommitmentFrames

/-! Instantiate the recorded-view word construction with the actual strictly
parsed commitment messages. No root-target equation or equality to supplied
word metadata is assumed. Actual verifier acceptance must still imply these
message/parser facts in the source-refinement layer. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawCutConstructedWords

open FS FS2 FS2.Duplex
open AspisV8R19.MemoizedProgramLaw AspisV8R19.AdaptiveFirstReadLaw
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open CanonicalCutEnrichedTranscript RawCutTranscriptRun RawCutProverCompiler

private theorem pred_getD_of_bind (o : Option Bytes) (j : Fin 11) (root : State)
    (h : o.bind (RawByteCollisionTargets.pred j) = some root) :
    RawByteCollisionTargets.pred j (o.getD []) = some root := by
  cases o with
  | none => cases h
  | some input => exact h

theorem initial_root (decoder : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (pub : RawCutProverCompiler.Public) (pf : RawCutProverCompiler.Proof)
    (root : State) (w : LiteralTranscript.C1Word)
    (h : pf 0 = .initial root w) :
    RawByteCollisionTargets.pred 8 (RawCutWordsFromView.frame decoder H pub pf 0) = some root := by
  unfold RawCutWordsFromView.frame
  apply pred_getD_of_bind
  change (firstCell (LiteralByteSampler.samp 0
    ((LiteralByteProtocol.protocol decoder).transcript H pub pf 0) (pf 0))).bind _ = _
  rw [h]
  exact RawCutCommitmentFrames.initial_root _ root w

theorem c2_root (decoder : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (pub : RawCutProverCompiler.Public) (pf : RawCutProverCompiler.Proof)
    (m : LiteralTranscript.BytesMessage) (w : LiteralTranscript.C2Word) (root : State)
    (h : pf 2 = .c2 m w)
    (hdecode : SemanticRecordCodec.decode ⟨2, by decide⟩ m.val =
      some ⟨.c2Root root, by rfl⟩) :
    RawByteCollisionTargets.pred 8 (RawCutWordsFromView.frame decoder H pub pf 2) = some root := by
  unfold RawCutWordsFromView.frame
  apply pred_getD_of_bind
  change (firstCell (LiteralByteSampler.samp 2
    ((LiteralByteProtocol.protocol decoder).transcript H pub pf 2) (pf 2))).bind _ = _
  rw [h]
  exact RawCutCommitmentFrames.c2_root _ m w root hdecode

theorem second_root (decoder : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (pub : RawCutProverCompiler.Public) (pf : RawCutProverCompiler.Proof)
    (m : LiteralTranscript.BytesMessage) (w : LiteralTranscript.VWord)
    (payload : OpeningRecordCodec.Payload .second)
    (h : pf 30 = .second m w)
    (hdecode : OpeningRecordCodec.decode .second m.val = some payload) :
    RawByteCollisionTargets.pred 9 (RawCutWordsFromView.frame decoder H pub pf 30) =
      some payload.1 := by
  unfold RawCutWordsFromView.frame
  apply pred_getD_of_bind
  change (firstCell (LiteralByteSampler.samp 30
    ((LiteralByteProtocol.protocol decoder).transcript H pub pf 30) (pf 30))).bind _ = _
  rw [h]
  exact RawCutCommitmentFrames.second_root _ m w payload hdecode

/-- With the existing strict parsers, the actual run's constructed words are
exactly its three full-log recovery maps outside the one shared exception. -/
theorem buildWords_eq_full_from_messages (decoder : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (H : Bytes → State)
    (iv : State) (Q : Nat)
    (hQ : firstReads emptyTable (eval H (experiment P (verifier decoder d))).1 ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv RawByteCollisionTargets.pred Q)
      emptyTable (eval H (experiment P (verifier decoder d))).1)
    (c1root : State) (c1 : LiteralTranscript.C1Word)
    (c2msg : LiteralTranscript.BytesMessage) (c2 : LiteralTranscript.C2Word) (c2root : State)
    (secondmsg : LiteralTranscript.BytesMessage) (final : LiteralTranscript.VWord)
    (second : OpeningRecordCodec.Payload .second)
    (h0 : (eval H (experiment P (verifier decoder d))).2.1.2 0 = .initial c1root c1)
    (h2 : (eval H (experiment P (verifier decoder d))).2.1.2 2 = .c2 c2msg c2)
    (h30 : (eval H (experiment P (verifier decoder d))).2.1.2 30 = .second secondmsg final)
    (hc2 : SemanticRecordCodec.decode ⟨2, by decide⟩ c2msg.val =
      some ⟨.c2Root c2root, by rfl⟩)
    (hsecond : OpeningRecordCodec.decode .second secondmsg.val = some second) :
    let v := eval H (experiment P (verifier decoder d))
    RawCutWordsFromView.buildWords decoder v =
      wordsFromMaps (fullC1Map v.1 c1root) (fullC2Map v.1 c2root)
        (fullFoldedMap v.1 second.1) := by
  let roots : Fin 3 → State := fun i =>
    if i.val = 0 then c1root else if i.val = 1 then c2root else second.1
  have result := RawCutWordsFromView.buildWords_eq_full decoder d P H iv Q hQ hout roots
    (initial_root decoder H _ _ c1root c1 h0)
    (c2_root decoder H _ _ c2msg c2 c2root h2 hc2)
    (second_root decoder H _ _ secondmsg final second h30 hsecond)
  simpa [roots] using result

#print axioms initial_root
#print axioms c2_root
#print axioms second_root
#print axioms buildWords_eq_full_from_messages
end AspisR1.RawCutConstructedWords
end
