import RawRecordedExtractorBranchTrace
import RawExtractorCostComposedBin

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace AspisR1.RawRecordedExtractorBranchTraceBin
open RawCutWordsFromRunExecutableBin RawCutWordsFromRunPublicValidBin
open RawRecordedExtractorBranchTrace (Event bindTrace two_bind_value two_bind_length)

attribute [local irreducible] runDecodedPublic
  GSConcreteByteDecoderBank.run LiteralComputedCandidateExtract.extract
  initialWordsFromRun finalWordFromRun
  AspisWide.GSConcreteReceivedWordInputs.fromWords

/-- Same calls and short-circuit branches as the actual extractor. -/
def extract (run : RawCutProverCompiler.RunView)
    (coins : GSConcreteByteDecoderBank.RawCoins) :
    Option SpendRelation.Wspend × List Event :=
  bindTrace (runDecodedPublic run) .parsePublic fun pub =>
    let W := initialWordsFromRun run
    let V := fun _ => finalWordFromRun run
    bindTrace (GSConcreteByteDecoderBank.run
      (AspisWide.GSConcreteReceivedWordInputs.fromWords W V) coins) .decoderBank
      fun out => (LiteralComputedCandidateExtract.extract pub W
        (GSByteJointSpendExtractor.decodedLists W out), [.candidateScan])

#check extract

theorem value (run : RawCutProverCompiler.RunView)
    (coins : GSConcreteByteDecoderBank.RawCoins) :
    (extract run coins).1 = RawRecordedPublicSpendExtractorBin.extract run coins := by
  change (bindTrace (runDecodedPublic run) .parsePublic (fun pub =>
    bindTrace (GSConcreteByteDecoderBank.run
      (AspisWide.GSConcreteReceivedWordInputs.fromWords
        (initialWordsFromRun run) (fun _ => finalWordFromRun run)) coins) .decoderBank
      (fun out => (LiteralComputedCandidateExtract.extract pub (initialWordsFromRun run)
        (GSByteJointSpendExtractor.decodedLists (initialWordsFromRun run) out),
        [.candidateScan])))).1 =
    (runDecodedPublic run).bind (fun pub =>
      (GSConcreteByteDecoderBank.run
        (AspisWide.GSConcreteReceivedWordInputs.fromWords
          (initialWordsFromRun run) (fun _ => finalWordFromRun run)) coins).bind
        (fun out => LiteralComputedCandidateExtract.extract pub (initialWordsFromRun run)
          (GSByteJointSpendExtractor.decodedLists (initialWordsFromRun run) out)))
  exact two_bind_value _ _ _ _ _ _

/-- At most one parse, one bank call and one candidate call; this says
nothing about the number of operations inside those calls. -/
theorem event_count (run : RawCutProverCompiler.RunView)
    (coins : GSConcreteByteDecoderBank.RawCoins) :
    (extract run coins).2.length ≤ 3 :=
  two_bind_length _ _ _ _ _ _

/-- Output equality is independent of the resource implementation. No default
resource labels and no ledger instance are supplied by this construction. -/
def attachResources
    (resources : RawCutProverCompiler.RunView → GSConcreteByteDecoderBank.RawCoins →
      RawExtractorCostComposedV2.Resources) : RawExtractorCostComposedBin.CostedExtractor where
  eval run coins := ((extract run coins).1, resources run coins)
  value := value

theorem attachResources_value
    (resources : RawCutProverCompiler.RunView → GSConcreteByteDecoderBank.RawCoins →
      RawExtractorCostComposedV2.Resources)
    (run : RawCutProverCompiler.RunView) (coins : GSConcreteByteDecoderBank.RawCoins) :
    ((attachResources resources).eval run coins).1 =
      RawRecordedPublicSpendExtractorBin.extract run coins :=
  (attachResources resources).value run coins

#print axioms value
#print axioms event_count
#print axioms attachResources_value
end AspisR1.RawRecordedExtractorBranchTraceBin
