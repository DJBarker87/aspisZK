import R1C1SemanticPadding
import R1IncrementalCandidateCost

/-! Focused checkpoint: reuse of the old semantic padding and exact joint
candidate specification by a bounded incremental merge. This is not an
implementation or complexity theorem for the supplied per-lane decoders. -/

#print axioms AspisR1.C1SemanticPadding.projectWord_eq_c2Words
#print axioms AspisR1.C1SemanticPadding.candidates_eq_old_Lambda
#print axioms AspisR1.IncrementalJointCandidates.advance_supported
#print axioms AspisR1.IncrementalJointCandidates.advance_card_le_100
#print axioms AspisR1.IncrementalJointCandidates.unfiltered_image_card_le
#print axioms AspisR1.IncrementalJointCandidates.unfiltered_image_card_le_10000
#print axioms AspisR1.IncrementalJointCandidates.projectMessage_insert
#print axioms AspisR1.IncrementalJointCandidates.selectedSupport_project
#print axioms AspisR1.IncrementalJointCandidates.projected_full_threshold
#print axioms AspisR1.IncrementalJointCandidates.advance_preserves_full_projection
#print axioms AspisR1.IncrementalCandidateLoop.run_supported
#print axioms AspisR1.IncrementalCandidateLoop.run_card_le_100
#print axioms AspisR1.IncrementalCandidateLoop.run_preserves_projection
#print axioms AspisR1.IncrementalCandidateLoop.run_close
#print axioms AspisR1.IncrementalCandidateLoop.full_candidate_coordinate_close
#print axioms AspisR1.IncrementalCandidateLoop.candidates_card
#print axioms AspisR1.IncrementalCandidateLoop.candidates_eq_lambda
#print axioms AspisR1.IncrementalCandidateCost.pairs_le
#print axioms AspisR1.IncrementalCandidateCost.initial_pairs_le
#print axioms AspisR1.IncrementalCandidateCost.initial_pairs_le_290000
