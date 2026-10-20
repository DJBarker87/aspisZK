import GSByteBankWorkM10
import GSPointBatchWorkM10
import GSPostProcessCompleteM10
import BinPublicRecoverySharedStageM10
import RawRecordedEagerExtractorReadsBin
import OptionWorkBoundM10

/-! Whole extractor work composition. Recovery/point arrays and the byte bank
are eager; public failure and private aborts still have the same returned
value. All later word reads use retained typed arrays. The sole component
premise is the fixed-shape public image inverse/check bound. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.ActualContinuationDefinitionM10
open AspisWideTower AspisV8R15.ExactTowerBase SpendRelation
open AspisPool.AlgorithmicCircleDecoderV7
open CanonicalCutEnrichedTranscript (Words)
open RawRecordedEagerExtractorReadsBin (RunView Coins continueWithWords)
open GSPostProcessWorkM10

def received (words : Words) : Fin 29 → InitialWord WideExact :=
  LiteralTypedWords.word ExactBaseProjection.embed (algebraMap QM31Exact WideExact) words.c1 words.c2

def continuation (image : PublicImage) (pub : R0P.Public M31Exact) (words : Words) (coins : Coins) :
    Option Wspend × Nat :=
  let W := received words
  let points := GSPointBatchWorkM10.inputs W (fun _ => words.final)
  let bank := GSByteBankWorkM10.run points.1 coins
  let post := PublicParserWork.bind (bank.1,0) (GSPostProcessCompleteM10.eval image pub W)
  (post.1,points.2+bank.2+post.2+1000)


end AspisR1.ActualContinuationDefinitionM10
end
