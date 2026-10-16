import RawCutOpeningWordProjection
import RawCutConstructedWords

/-! Specialize raw-cut opening projection to the words constructed by the
recorded verifier run. Frame reads and commitment roots are recovered from
the actual messages using the existing sampler/parser lemmas. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawCutRecordedRunOpeningProjection

open AspisR1.RawCutOpeningWordProjection
open AspisR1.RawCutTranscriptRun
open AspisR1.RawCutProverCompiler
open AspisR1.RawCutWordsFromView
open AspisR1.RawCutConstructedWords
open AspisR1.LiteralOpeningView
open AspisR1.TypedRecoveredWords
open AspisR1.FoldedLeafCodec
open AspisR1.FoldedRecoveredWord
open AspisR1.MixedLeafDecoder
open AspisR1.CanonicalCutTypedProjection
open AspisR1.MerkleIndexGeometry
open Merkle32Path Merkle32Leaf MerkleTable MerkleLeafRecovery MerkleRecordedLog
open FS FS2 FS2.Duplex AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

/-- The literal opening projection for the actual constructed words of a
recorded experiment run. The frame and root parameters of the generic raw-cut
lemma are discharged from the run's three typed commitment messages. -/
theorem recorded_run_openings_project_constructed_words
    (decoder : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (H : Bytes → State)
    (run : RawCutProverCompiler.RunView)
    (hrun : run = eval H (experiment P (verifier decoder d)))
    (iv : State) (Q : Nat)
    (hQ : firstReads emptyTable run.1 ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv RawByteCollisionTargets.pred Q)
      emptyTable run.1)
    (c1root : State) (c1 : LiteralTranscript.C1Word)
    (c2msg : LiteralTranscript.BytesMessage) (c2 : LiteralTranscript.C2Word)
    (c2root : State)
    (secondmsg : LiteralTranscript.BytesMessage) (final : LiteralTranscript.VWord)
    (second : OpeningRecordCodec.Payload .second)
    (h0 : run.2.1.2 0 = .initial c1root c1)
    (h2 : run.2.1.2 2 = .c2 c2msg c2)
    (h30 : run.2.1.2 30 = .second secondmsg final)
    (hc2 : SemanticRecordCodec.decode ⟨2, by decide⟩ c2msg.val =
      some ⟨.c2Root c2root, by rfl⟩)
    (hsecond : OpeningRecordCodec.decode .second secondmsg.val = some second)
    (readerView : LiteralOpeningView.View)
    (hreadOpening : LiteralOpeningView.read
      ((LiteralByteProtocol.protocol decoder).transcript H
        run.2.1.1 run.2.1.2 33).rounds =
          some readerView)
    (q : Fin 262144)
    (packed1 salt1 : List ExactLeafFieldCodec.Byte)
    (hw1 : packed1.length = 480) (hs1 : salt1.length = 32)
    {slots1 : List (Fin 8)} (path1 : Path slots1)
    (haccept1 : (eval H (MerkleProgram.leafProgram path1
      (leafInput 0x71 packed1 salt1))).2 = c1root)
    (hopen1 : ∀ a, Read (eval H (MerkleProgram.leafProgram path1
      (leafInput 0x71 packed1 salt1))).1 a →
        Read run.1 a)
    (payload1 : TypedRecoveredWords.C1)
    (hdecode1 : decodeC1 packed1 = some payload1)
    (packed2 salt2 : List ExactLeafFieldCodec.Byte)
    (hw2 : packed2.length = 128) (hs2 : salt2.length = 32)
    {slots2 : List (Fin 8)} (path2 : Path slots2)
    (haccept2 : (eval H (MerkleProgram.leafProgram path2
      (leafInput 0xf1 packed2 salt2))).2 = c2root)
    (hopen2 : ∀ a, Read (eval H (MerkleProgram.leafProgram path2
      (leafInput 0xf1 packed2 salt2))).1 a →
        Read run.1 a)
    (payload2 : TypedRecoveredWords.C2)
    (hdecode2 : decodeC2 packed2 = some payload2)
    (packedF saltF : List ExactLeafFieldCodec.Byte)
    (hwF : packedF.length = 128) (hsF : saltF.length = 32)
    {slotsF : List (Fin 8)} (pathF : Path slotsF)
    (hacceptF : (eval H (MerkleProgram.leafProgram pathF
      (leafInput 0x72 packedF saltF))).2 = second.1)
    (hopenF : ∀ a, Read (eval H (MerkleProgram.leafProgram pathF
      (leafInput 0x72 packedF saltF))).1 a →
        Read run.1 a)
    (payloadF : FoldedLeafCodec.Folded)
    (hdecodeF : decodeFolded packedF = some payloadF)
    (hslots1 : slots1 = MerkleIndexGeometry.slots 6
      (queryLeaf (CanonicalCutTypedProjection.queryPosition q)).val)
    (hslots2 : slots2 = MerkleIndexGeometry.slots 6
      (queryLeaf (CanonicalCutTypedProjection.queryPosition q)).val)
    (hslotsF : slotsF = MerkleIndexGeometry.slots 6 (foldedIndex q).val) :
    ∃ v',
      LiteralOpeningView.read
        (CanonicalCutEnrichedTranscript.enrichRounds
          (RawCutWordsFromView.buildWords decoder run)
          ((LiteralByteProtocol.protocol decoder).transcript H
            run.2.1.1 run.2.1.2 33).rounds) = some v' ∧
      v'.semantic.map Prod.snd = readerView.semantic.map Prod.snd ∧
      (∀ l : Fin 26,
        v'.word ⟨l.val, by have hl := l.isLt; omega⟩
          (CanonicalCutTypedProjection.queryPosition q) =
          ExactBaseProjection.embed ((payload1 (querySlot
            (CanonicalCutTypedProjection.queryPosition q))).1 l)) ∧
      v'.word ⟨26, by decide⟩ (CanonicalCutTypedProjection.queryPosition q) =
        LiteralOpeningView.eK ((payload2 (querySlot
          (CanonicalCutTypedProjection.queryPosition q))) ⟨0, by decide⟩) ∧
      v'.word ⟨27, by decide⟩ (CanonicalCutTypedProjection.queryPosition q) =
        LiteralOpeningView.eK ((payload2 (querySlot
          (CanonicalCutTypedProjection.queryPosition q))) ⟨1, by decide⟩) ∧
      v'.word ⟨28, by decide⟩ (CanonicalCutTypedProjection.queryPosition q) =
        LiteralOpeningView.eK ((payload1 (querySlot
          (CanonicalCutTypedProjection.queryPosition q))).2) ∧
      (RawCutWordsFromView.buildWords decoder run).final q =
        payloadF (foldedSlot q) := by
  let f0 := RawCutWordsFromView.frame decoder H run.2.1.1 run.2.1.2 0
  let f2 := RawCutWordsFromView.frame decoder H run.2.1.1 run.2.1.2 2
  let f30 := RawCutWordsFromView.frame decoder H run.2.1.1 run.2.1.2 30
  let rs := (LiteralByteProtocol.protocol decoder).transcript H
    run.2.1.1 run.2.1.2 33 |>.rounds
  have hcons : ∀ a ∈ run.1, a.2 = H a.1 := by
    rw [hrun]
    exact FS.eval_consistent H _
  have hread0 : Read run.1 f0 := by
    change Read run.1 (RawCutWordsFromView.frame decoder H
      run.2.1.1 run.2.1.2 0)
    rw [hrun]
    exact RawCutWordsFromView.frame_read decoder d P H 0 (by decide)
  have hread2 : Read run.1 f2 := by
    change Read run.1 (RawCutWordsFromView.frame decoder H
      run.2.1.1 run.2.1.2 2)
    rw [hrun]
    exact RawCutWordsFromView.frame_read decoder d P H 2 (by decide)
  have hread30 : Read run.1 f30 := by
    change Read run.1 (RawCutWordsFromView.frame decoder H
      run.2.1.1 run.2.1.2 30)
    rw [hrun]
    exact RawCutWordsFromView.frame_read decoder d P H 30 (by decide)
  have hroot0 : RawByteCollisionTargets.pred 8 f0 = some c1root := by
    change RawByteCollisionTargets.pred 8 (RawCutWordsFromView.frame decoder H
      run.2.1.1 run.2.1.2 0) = some c1root
    rw [hrun]
    have h0' : (eval H (experiment P (verifier decoder d))).2.1.2 0 =
        .initial c1root c1 := by rw [← hrun]; exact h0
    exact RawCutConstructedWords.initial_root decoder H
      (eval H (experiment P (verifier decoder d))).2.1.1
      (eval H (experiment P (verifier decoder d))).2.1.2 c1root c1 h0'
  have hroot2 : RawByteCollisionTargets.pred 8 f2 = some c2root := by
    change RawByteCollisionTargets.pred 8 (RawCutWordsFromView.frame decoder H
      run.2.1.1 run.2.1.2 2) = some c2root
    rw [hrun]
    have h2' : (eval H (experiment P (verifier decoder d))).2.1.2 2 =
        .c2 c2msg c2 := by rw [← hrun]; exact h2
    exact RawCutConstructedWords.c2_root decoder H
      (eval H (experiment P (verifier decoder d))).2.1.1
      (eval H (experiment P (verifier decoder d))).2.1.2 c2msg c2 c2root h2' hc2
  have hroot30 : RawByteCollisionTargets.pred 9 f30 = some second.1 := by
    change RawByteCollisionTargets.pred 9 (RawCutWordsFromView.frame decoder H
      run.2.1.1 run.2.1.2 30) = some second.1
    rw [hrun]
    have h30' : (eval H (experiment P (verifier decoder d))).2.1.2 30 =
        .second secondmsg final := by rw [← hrun]; exact h30
    exact RawCutConstructedWords.second_root decoder H
      (eval H (experiment P (verifier decoder d))).2.1.1
      (eval H (experiment P (verifier decoder d))).2.1.2
      secondmsg final second h30' hsecond
  have hwords : RawCutWordsFromView.buildWords decoder run =
      CanonicalCutEnrichedTranscript.wordsFromRawCuts run.1 f0 f2 f30
        c1root c2root second.1 := by
    have hwords' := RawCutWordsFromView.buildWords_eq_actual_cuts decoder d P H
    rw [← hrun] at hwords'
    simpa only [f0, f2, f30, RawCutWordsFromView.rootFrom,
      hroot0, hroot2, hroot30, Option.getD_some] using hwords'
  exact actual_raw_cut_openings_project_literal_word
    iv H run.1 Q hcons hQ hout
    f0 f2 f30 c1root c2root second.1 hread0 hread2 hread30 hroot0 hroot2 hroot30
    (RawCutWordsFromView.buildWords decoder run) hwords rs readerView hreadOpening q
    packed1 salt1 hw1 hs1 path1 haccept1 hopen1 payload1 hdecode1
    packed2 salt2 hw2 hs2 path2 haccept2 hopen2 payload2 hdecode2
    packedF saltF hwF hsF pathF hacceptF hopenF payloadF hdecodeF
    hslots1 hslots2 hslotsF

#print axioms recorded_run_openings_project_constructed_words

end AspisR1.RawCutRecordedRunOpeningProjection
end
