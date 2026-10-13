import R1SemanticOpening
import R1SamplerWordPass
import R0.OpeningDefinitions
import R0P.MessageDescent
import Wide.SubfieldDescent
import Wide.Instances

/-! One combined focused replay after the reuse/refactor predecessors passed.
This audits component proof dependencies and import coexistence. It is not a
full source-manifest replay or an end-to-end security theorem. -/

#print axioms AspisR1.SemanticOpening.large_matching_implies_witness
#print axioms AspisR1.SemanticOpening.witness_rows_typed
#print axioms AspisR1.CandidateDescent.large_matching_implies_typed_claims
#print axioms AspisR1.SamplerWordPass.machineProcess_correct
#print axioms AspisWide.SubfieldDescent.initialMessage_subfield_descent
#print axioms AspisWide.SubfieldDescent.wideInitialCodeword_subfield_descent
#print axioms AspisR0.Opening.dot_coeffWeight_left
#print axioms AspisR0.Opening.dot_coeffWeight_indicator
#print axioms AspisR0.RoundNormalization.cited_round_identities
#print axioms AspisWide.Instances.wideInitialWidth29CurveDecodable
#print axioms AspisWide.Instances.wideFinalDegreeThreeCurveDecodable
#print axioms AspisWideTower.wideExact_card
