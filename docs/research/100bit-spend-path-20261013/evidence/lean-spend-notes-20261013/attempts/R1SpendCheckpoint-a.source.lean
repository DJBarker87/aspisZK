import R1SpendExtraction
import R1SemanticPrefix

/-! Focused combined import and axiom audit for note-level semantic extraction.
No shared-oracle, append-transition, Rust-refinement, or privacy release is
asserted. All historical dependencies are reused from the pinned cache. -/
#print axioms AspisR1.SpendValues.of_value_balance
#print axioms AspisR1.OutputCopyLinks.change_cells
#print axioms AspisR1.OutputCopyLinks.recipient_cells
#print axioms AspisR1.OutputNotes.change_public
#print axioms AspisR1.OutputNotes.recipient_public
#print axioms AspisR1.SpendSemantics.of_production
#print axioms AspisR1.SpendExtraction.strengthen_candidate_result
#print axioms AspisR1.SpendExtraction.large_matching_extracts
