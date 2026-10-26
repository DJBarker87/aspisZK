import ComposedContinuationSpecM10
import BinPublicRecoverySharedStageM10
import RawRecordedEagerExtractorReadsBin
import PublicParsedIndexM10
import ExtractorStagesM10

/-! Complete writer-valued extractor. The continuation body is a projection
from an irreducible stage certificate, not an unfolded concrete computation. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.CostedExtractorStagesM10
open AspisWideTower AspisV8R15.ExactTowerBase SpendRelation
open AspisPool.AlgorithmicCircleDecoderV7
open CanonicalCutEnrichedTranscript (Words)
open RawRecordedEagerExtractorReadsBin (RunView Coins continueWithWords)
open GSPostProcessWorkM10
attribute [local irreducible] GSByteJointSpendExtractor.extract BinEagerWordsReads.words
  BinPublicRecoverySharedStageM10.stage PublicParserWork.parsePublic
  RawRecordedPublicSpendExtractorBin.extract RawCutWordsFromRunPublicValidBin.runDecodedPublic
  ComposedContinuationSpecM10.budget

@[irreducible] def received (words : Words) : Fin 29 → InitialWord WideExact :=
  LiteralTypedWords.word ExactBaseProjection.embed (algebraMap QM31Exact WideExact) words.c1 words.c2

@[irreducible] def continuation (image : PublicImage) (C : Nat) (hi : PublicImageBound image C)
    (pub : R0P.Public M31Exact) (words : Words) (coins : Coins) : Option Wspend × Nat :=
  (ComposedContinuationSpecM10.spec image C hi pub (received words) coins).run
    (received words,fun _ => words.final)

theorem continuation_value (image : PublicImage) (C : Nat) (hi : PublicImageBound image C)
    (pub : R0P.Public M31Exact) (words : Words) (coins : Coins) :
    (continuation image C hi pub words coins).1 = continueWithWords pub words coins := by
  unfold continuation
  have h := ComposedContinuationSpecM10.value image C hi pub (received words) (fun _ => words.final) coins
  simpa only [received,continueWithWords] using h

theorem continuation_work (image : PublicImage) (C : Nat) (hi : PublicImageBound image C)
    (pub : R0P.Public M31Exact) (hp : pub.nextPairIndex < 2^64) (words : Words) (coins : Coins) :
    (continuation image C hi pub words coins).2 ≤ ComposedContinuationSpecM10.budget C := by
  unfold continuation
  exact ComposedContinuationSpecM10.work image C hi pub hp _ _ coins

@[irreducible] def eval (image : PublicImage) (C : Nat) (hi : PublicImageBound image C)
    (run : RunView) (coins : Coins) : Option Wspend × Nat :=
  ExtractorStagesM10.publicStage (BinPublicRecoverySharedStageM10.stage run)
    (PublicParserWork.parsePublic run.2.1.1.pubBytes)
    (fun pub words => continuation image C hi pub words coins)

theorem value (image : PublicImage) (C : Nat) (hi : PublicImageBound image C)
    (run : RunView) (coins : Coins) :
    (eval image C hi run coins).1 = RawRecordedPublicSpendExtractorBin.extract run coins := by
  have hp : (PublicParserWork.parsePublic run.2.1.1.pubBytes).1 =
      RawCutWordsFromRunPublicValidBin.runDecodedPublic run := by
    unfold RawCutWordsFromRunPublicValidBin.runDecodedPublic
    exact PublicParserWork.parsePublic_value _
  have hh := ExtractorStagesM10.public_refines (BinPublicRecoverySharedStageM10.stage run)
    (PublicParserWork.parsePublic run.2.1.1.pubBytes)
    (fun pub words => continuation image C hi pub words coins)
    (BinEagerWordsReads.words run).1 (RawCutWordsFromRunPublicValidBin.runDecodedPublic run)
    (fun pub words => continueWithWords pub words coins)
    (BinPublicRecoverySharedStageM10.stage_value run) hp
    (fun pub words => continuation_value image C hi pub words coins)
  have he := RawRecordedEagerExtractorReadsBin.optionReads_value
    (RawCutWordsFromRunPublicValidBin.runDecodedPublic run)
    (fun pub => (continueWithWords pub (BinEagerWordsReads.words run).1 coins,
      (BinEagerWordsReads.words run).2))
  unfold eval
  exact (hh.trans he.symm).trans (RawRecordedEagerExtractorReadsBin.value run coins)

@[never_extract,noinline,irreducible] def workConstant (C : Nat) : Nat :=
  4000000000000+110260+ComposedContinuationSpecM10.budget C+1+1000

theorem work (image : PublicImage) (C : Nat) (hi : PublicImageBound image C)
    (run : RunView) (coins : Coins) :
    (eval image C hi run coins).2 ≤ workConstant C*(run.1.length+1) := by
  have hh := ExtractorStagesM10.public_work (BinPublicRecoverySharedStageM10.stage run)
    (PublicParserWork.parsePublic run.2.1.1.pubBytes)
    (fun pub words => continuation image C hi pub words coins)
    (4000000000000*(run.1.length+1)) 110260 (ComposedContinuationSpecM10.budget C)
    (BinPublicRecoverySharedStageM10.stage_work run) (PublicParserWork.parsePublic_work _)
    (fun pub hpub => continuation_work image C hi pub (PublicParsedIndexM10.bound _ pub hpub) _ coins)
  have hc : 110260+ComposedContinuationSpecM10.budget C+1+1000 ≤
      (110260+ComposedContinuationSpecM10.budget C+1+1000)*(run.1.length+1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  unfold eval workConstant
  nlinarith

#print axioms continuation_value
#print axioms continuation_work
#print axioms value
#print axioms work
end AspisR1.CostedExtractorStagesM10
end
