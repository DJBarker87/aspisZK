import R0.RoundNormalization
import Wide.MatchedInstances
import Wide.JointList
import Wide.SubfieldDescent

/-! Integration and axiom audit. The opening-layer theorem is deliberately
absent: R0_SOUNDNESS.md gap 13 records the stopped F5/(V2) comparison.
The literal V8 citation audit is separate because its natural-basis names
conflict with the pinned V7 names required by Wide. -/

#print axioms AspisR0.Fold.F4
#print axioms AspisR0.Fold.wideF4
#print axioms AspisR0.RoundNormalization.wide_cited_round_identities
#print axioms AspisR0.RoundNormalization.wide_unscaled_F5_counterexample
#print axioms AspisR0.RoundNormalization.comparison_step_counterexample
#print axioms AspisWide.Instances.wideInitialWidth29CurveDecodable
#print axioms AspisWide.Instances.wideFinalDegreeThreeCurveDecodable
#print axioms AspisWide.MatchedInstances.wideFinal_bad_response_challenges_card_le
#print axioms AspisWide.JointList.wideJointInitialCodewords_card_le_100
#print axioms AspisWide.SubfieldDescent.wideInitialCodeword_subfield_descent
