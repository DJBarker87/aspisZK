import ActualResourceEvalM10

set_option autoImplicit false
noncomputable section
namespace AspisR1.ActualCostedExtractorM10

@[never_extract,noinline,irreducible] def extractor : RawExtractorCostComposedBin.CostedExtractor :=
  ⟨ActualResourceEvalM10.eval,ActualResourceEvalM10.value⟩

theorem value (run : RawRecordedEagerExtractorReadsBin.RunView)
    (coins : RawRecordedEagerExtractorReadsBin.Coins) :
    (extractor.eval run coins).1 = RawRecordedPublicSpendExtractorBin.extract run coins := by
  unfold extractor
  exact ActualResourceEvalM10.value run coins

#print axioms value
end AspisR1.ActualCostedExtractorM10
end
