import BinCompiledRunWordStability
import LiteralTableWordChoiceBin
import LiteralTableChoiceRun
import RWireRawCutLaterTableLiteralWords

/-! The concrete decoder's current-table words agree, component by component,
with the recorded full-log words as soon as each commitment has appeared. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RWireLiteralTableChoiceWords
open FS FS2 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open LiteralDecoderEnrichment
open CanonicalCutEnrichedTranscript (Words wordsFromMaps enrichPrefix enrichMessage)
open BinCanonicalCutWords

def atRun (decoder : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (run : RawCutProverCompiler.RunView) (n : Nat) : Words :=
  let frame := RawCutWordsFromView.frame decoder H run.2.1.1 run.2.1.2 n
  LiteralTableWordChoiceBin.choose frame (tableBefore emptyTable run.1 frame)
    (LiteralTranscript.erasePrefix ((LiteralByteProtocol.protocol decoder).transcript H
      run.2.1.1 run.2.1.2 n)) (LiteralTranscript.erase (run.2.1.2 n))

theorem components (decoder : LiteralByteProtocol.Decoder)
    (d : RawCutTranscriptRun.ErasedPrefix → RawCutTranscriptRun.ErasedMessage → Bool)
    (prover : RawCutProverCompiler.Prover) (H : Bytes → State) (run : RawCutProverCompiler.RunView)
    (hrun : run = eval H (RawCutProverCompiler.experiment prover (RawCutProverCompiler.verifier decoder d)))
    (iv : State) (Q : Nat) (hQ : firstReads emptyTable run.1 ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q) emptyTable run.1)
    (hvalid : ∀ i < 33, LiteralTranscript.valid i (run.2.1.2 i)) (n : Nat) (hn : n < 33)
    (r1 : State) (w1 : LiteralTranscript.C1Word)
    (b2 : LiteralTranscript.BytesMessage) (w2 : LiteralTranscript.C2Word) (r2 : State)
    (b30 : LiteralTranscript.BytesMessage) (w30 : LiteralTranscript.VWord)
    (v30 : OpeningRecordCodec.Payload .second)
    (h0 : run.2.1.2 0 = .initial r1 w1)
    (h2 : run.2.1.2 2 = .c2 b2 w2)
    (h30 : run.2.1.2 30 = .second b30 w30)
    (hp2 : SemanticRecordCodec.decode ⟨2,by decide⟩ b2.val = some ⟨.c2Root r2,by rfl⟩)
    (hp30 : OpeningRecordCodec.decode .second b30.val = some v30) :
    let w := atRun decoder H run n
    let W := wordsFromMaps (fullC1Map run.1 r1) (fullC2Map run.1 r2) (fullFoldedMap run.1 v30.1)
    w.c1 = W.c1 ∧ (2 ≤ n → w.c2 = W.c2) ∧ (30 ≤ n → w.final = W.final) := by
  dsimp only
  let frame := RawCutWordsFromView.frame decoder H run.2.1.1 run.2.1.2 n
  let T := tableBefore emptyTable run.1 frame
  let P := LiteralTranscript.erasePrefix ((LiteralByteProtocol.protocol decoder).transcript H
    run.2.1.1 run.2.1.2 n)
  let m := LiteralTranscript.erase (run.2.1.2 n)
  refine ⟨?_,?_,?_⟩
  · have hr := LiteralTableChoiceRun.c1_root decoder H run.2.1.1 run.2.1.2 n r1 w1 h0
    have hm := RWireRawCutLaterTableLiteralWords.actual_c1_map_eq_current_table
      decoder d prover H run hrun iv Q hQ hout hvalid n hn (by omega) r1 w1 h0
    change fullC1Map run.1 r1 = RWireRawByteTableWords.c1Map T r1 at hm
    change TypedRecoveredWords.c1Value (RWireRawByteTableWords.c1Map T (LiteralTableWordChoice.c1Root P m)) =
      TypedRecoveredWords.c1Value (fullC1Map run.1 r1)
    rw [hr]
    exact congrArg TypedRecoveredWords.c1Value hm.symm
  · intro hn2
    have hr := LiteralTableChoiceRun.c2_root decoder H run.2.1.1 run.2.1.2 n hn2 b2 w2 r2 h2 hp2
    have hm := RWireRawCutLaterTableLiteralWords.actual_c2_map_eq_current_table
      decoder d prover H run hrun iv Q hQ hout hvalid n hn hn2 r2 b2 w2 h2 hp2
    change fullC2Map run.1 r2 = RWireRawByteTableWords.c2Map T r2 at hm
    change TypedRecoveredWords.c2Value (RWireRawByteTableWords.c2Map T (LiteralTableWordChoice.c2Root P m)) =
      TypedRecoveredWords.c2Value (fullC2Map run.1 r2)
    rw [hr]
    exact congrArg TypedRecoveredWords.c2Value hm.symm
  · intro hn30
    have hr := LiteralTableChoiceRun.final_root decoder H run.2.1.1 run.2.1.2 n hn30 b30 w30 v30 h30 hp30
    have hm := RWireRawCutLaterTableLiteralWords.actual_folded_map_eq_current_table
      decoder d prover H run hrun iv Q hQ hout hvalid n hn hn30 b30 w30 v30 h30 hp30
    change fullFoldedMap run.1 v30.1 = RWireRawByteTableWords.foldedMap T v30.1 at hm
    change (fun q => FoldedRecoveredWord.wordOfPacked
      ((RWireRawByteTableWords.foldedMap T (LiteralTableWordChoice.finalRoot P m))
        (MerkleIndexGeometry.foldedIndex q)) q) =
      (fun q => FoldedRecoveredWord.wordOfPacked
        ((fullFoldedMap run.1 v30.1) (MerkleIndexGeometry.foldedIndex q)) q)
    rw [hr,← hm]

theorem constructed_components (decoder : LiteralByteProtocol.Decoder)
    (d : RawCutTranscriptRun.ErasedPrefix → RawCutTranscriptRun.ErasedMessage → Bool)
    (prover : RawCutProverCompiler.Prover) (H : Bytes → State) (run : RawCutProverCompiler.RunView)
    (hrun : run = eval H (RawCutProverCompiler.experiment prover (RawCutProverCompiler.verifier decoder d)))
    (iv : State) (Q : Nat) (hQ : firstReads emptyTable run.1 ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q) emptyTable run.1)
    (hvalid : ∀ i < 33, LiteralTranscript.valid i (run.2.1.2 i)) (n : Nat) (hn : n < 33)
    (r1 : State) (w1 : LiteralTranscript.C1Word)
    (b2 : LiteralTranscript.BytesMessage) (w2 : LiteralTranscript.C2Word) (r2 : State)
    (b30 : LiteralTranscript.BytesMessage) (w30 : LiteralTranscript.VWord)
    (v30 : OpeningRecordCodec.Payload .second)
    (h0 : run.2.1.2 0 = .initial r1 w1)
    (h2 : run.2.1.2 2 = .c2 b2 w2)
    (h30 : run.2.1.2 30 = .second b30 w30)
    (hp2 : SemanticRecordCodec.decode ⟨2,by decide⟩ b2.val = some ⟨.c2Root r2,by rfl⟩)
    (hp30 : OpeningRecordCodec.decode .second b30.val = some v30) :
    let w := atRun decoder H run n
    let W := BinCompiledRunWordStability.wordsFromRun decoder run
    w.c1 = W.c1 ∧ (2 ≤ n → w.c2 = W.c2) ∧ (30 ≤ n → w.final = W.final) := by
  dsimp only
  have hc := components decoder d prover H run hrun iv Q hQ hout hvalid n hn
    r1 w1 b2 w2 r2 b30 w30 v30 h0 h2 h30 hp2 hp30
  have hb : BinCompiledRunWordStability.wordsFromRun decoder run =
      wordsFromMaps (fullC1Map run.1 r1) (fullC2Map run.1 r2) (fullFoldedMap run.1 v30.1) := by
    subst run
    exact RWireConstructedWords.buildWords_eq_full_from_messages decoder d prover H iv Q
      hQ hout r1 w1 b2 w2 r2 b30 w30 v30 h0 h2 h30 hp2 hp30
  rw [hb]
  exact hc

#print axioms components
#print axioms constructed_components

end AspisR1.RWireLiteralTableChoiceWords
end
