import R22TotalCheckedComposition
import R22Stage2LeafTotal

/-! All nineteen nullary extracted stage-2 layout computations. Their proved
totalities discharge the checked-success premise. Translation remains P6. -/
set_option autoImplicit false
namespace AspisR1.R22TotalStage2Constants
open Aeneas Aeneas.Std Result R22TotalCheckedComposition AspisR1Stage2

theorem compact_SEMANTIC_COMPACT_VALUES_R22
    (t : Translation (fun _ : Unit => compact.SEMANTIC_COMPACT_VALUES)) :
    ∀ u, NoOverflow (t.code u) ∧ wrapping (t.code u) = ok 426#usize := by
  apply total_refinement_R22 t.code (fun _ => 426#usize)
  intro u
  exact (t.source u).trans r22_compact_SEMANTIC_COMPACT_VALUES_total

#print axioms compact_SEMANTIC_COMPACT_VALUES_R22

theorem verifier_SEMANTIC_BYTES_R22
    (t : Translation (fun _ : Unit => verifier.SEMANTIC_BYTES)) :
    ∀ u, NoOverflow (t.code u) ∧ wrapping (t.code u) = ok 13831#usize := by
  apply total_refinement_R22 t.code (fun _ => 13831#usize)
  intro u
  exact (t.source u).trans r22_verifier_SEMANTIC_BYTES_total

#print axioms verifier_SEMANTIC_BYTES_R22

theorem compact_LOGICAL_SEMANTIC_R22
    (t : Translation (fun _ : Unit => compact.LOGICAL_SEMANTIC)) :
    ∀ u, NoOverflow (t.code u) ∧ wrapping (t.code u) = ok 13831#usize := by
  apply total_refinement_R22 t.code (fun _ => 13831#usize)
  intro u
  exact (t.source u).trans r22_compact_LOGICAL_SEMANTIC_total

#print axioms compact_LOGICAL_SEMANTIC_R22

theorem compact_COMPACT_SEMANTIC_R22
    (t : Translation (fun _ : Unit => compact.COMPACT_SEMANTIC)) :
    ∀ u, NoOverflow (t.code u) ∧ wrapping (t.code u) = ok 7015#usize := by
  apply total_refinement_R22 t.code (fun _ => 7015#usize)
  intro u
  exact (t.source u).trans r22_compact_COMPACT_SEMANTIC_total

#print axioms compact_COMPACT_SEMANTIC_R22

theorem compact_OFF_Y1_R22
    (t : Translation (fun _ : Unit => compact.OFF_Y1)) :
    ∀ u, NoOverflow (t.code u) ∧ wrapping (t.code u) = ok 7031#usize := by
  apply total_refinement_R22 t.code (fun _ => 7031#usize)
  intro u
  exact (t.source u).trans r22_compact_OFF_Y1_total

#print axioms compact_OFF_Y1_R22

theorem compact_COMPACT_Y1_R22
    (t : Translation (fun _ : Unit => compact.COMPACT_Y1)) :
    ∀ u, NoOverflow (t.code u) ∧ wrapping (t.code u) = ok 464#usize := by
  apply total_refinement_R22 t.code (fun _ => 464#usize)
  intro u
  exact (t.source u).trans r22_compact_COMPACT_Y1_total

#print axioms compact_COMPACT_Y1_R22

theorem compact_OFF_INACTIVE_R22
    (t : Translation (fun _ : Unit => compact.OFF_INACTIVE)) :
    ∀ u, NoOverflow (t.code u) ∧ wrapping (t.code u) = ok 7495#usize := by
  apply total_refinement_R22 t.code (fun _ => 7495#usize)
  intro u
  exact (t.source u).trans r22_compact_OFF_INACTIVE_total

#print axioms compact_OFF_INACTIVE_R22

theorem compact_OFF_ROUND0_R22
    (t : Translation (fun _ : Unit => compact.OFF_ROUND0)) :
    ∀ u, NoOverflow (t.code u) ∧ wrapping (t.code u) = ok 7527#usize := by
  apply total_refinement_R22 t.code (fun _ => 7527#usize)
  intro u
  exact (t.source u).trans r22_compact_OFF_ROUND0_total

#print axioms compact_OFF_ROUND0_R22

theorem compact_OFF_FOLDED_ROOT_R22
    (t : Translation (fun _ : Unit => compact.OFF_FOLDED_ROOT)) :
    ∀ u, NoOverflow (t.code u) ∧ wrapping (t.code u) = ok 7751#usize := by
  apply total_refinement_R22 t.code (fun _ => 7751#usize)
  intro u
  exact (t.source u).trans r22_compact_OFF_FOLDED_ROOT_total

#print axioms compact_OFF_FOLDED_ROOT_R22

theorem compact_OFF_ROUND1_R22
    (t : Translation (fun _ : Unit => compact.OFF_ROUND1)) :
    ∀ u, NoOverflow (t.code u) ∧ wrapping (t.code u) = ok 7783#usize := by
  apply total_refinement_R22 t.code (fun _ => 7783#usize)
  intro u
  exact (t.source u).trans r22_compact_OFF_ROUND1_total

#print axioms compact_OFF_ROUND1_R22

theorem compact_OFF_FINAL_R22
    (t : Translation (fun _ : Unit => compact.OFF_FINAL)) :
    ∀ u, NoOverflow (t.code u) ∧ wrapping (t.code u) = ok 8007#usize := by
  apply total_refinement_R22 t.code (fun _ => 8007#usize)
  intro u
  exact (t.source u).trans r22_compact_OFF_FINAL_total

#print axioms compact_OFF_FINAL_R22

theorem compact_OFF_OPENINGS_R22
    (t : Translation (fun _ : Unit => compact.OFF_OPENINGS)) :
    ∀ u, NoOverflow (t.code u) ∧ wrapping (t.code u) = ok 10055#usize := by
  apply total_refinement_R22 t.code (fun _ => 10055#usize)
  intro u
  exact (t.source u).trans r22_compact_OFF_OPENINGS_total

#print axioms compact_OFF_OPENINGS_R22

theorem compact_OPENING_R22
    (t : Translation (fun _ : Unit => compact.OPENING)) :
    ∀ u, NoOverflow (t.code u) ∧ wrapping (t.code u) = ok 832#usize := by
  apply total_refinement_R22 t.code (fun _ => 832#usize)
  intro u
  exact (t.source u).trans r22_compact_OPENING_total

#print axioms compact_OPENING_R22

theorem compact_OFF_NODES_R22
    (t : Translation (fun _ : Unit => compact.OFF_NODES)) :
    ∀ u, NoOverflow (t.code u) ∧ wrapping (t.code u) = ok 28359#usize := by
  apply total_refinement_R22 t.code (fun _ => 28359#usize)
  intro u
  exact (t.source u).trans r22_compact_OFF_NODES_total

#print axioms compact_OFF_NODES_R22

theorem compact_MAX_NODES_R22
    (t : Translation (fun _ : Unit => compact.MAX_NODES)) :
    ∀ u, NoOverflow (t.code u) ∧ wrapping (t.code u) = ok 914#usize := by
  apply total_refinement_R22 t.code (fun _ => 914#usize)
  intro u
  exact (t.source u).trans r22_compact_MAX_NODES_total

#print axioms compact_MAX_NODES_R22

theorem compact_FIXED_R22
    (t : Translation (fun _ : Unit => compact.FIXED)) :
    ∀ u, NoOverflow (t.code u) ∧ wrapping (t.code u) = ok 28359#usize := by
  apply total_refinement_R22 t.code (fun _ => 28359#usize)
  intro u
  exact (t.source u).trans r22_compact_FIXED_total

#print axioms compact_FIXED_R22

theorem compact_MAX_PROOF_R22
    (t : Translation (fun _ : Unit => compact.MAX_PROOF)) :
    ∀ u, NoOverflow (t.code u) ∧ wrapping (t.code u) = ok 57607#usize := by
  apply total_refinement_R22 t.code (fun _ => 57607#usize)
  intro u
  exact (t.source u).trans r22_compact_MAX_PROOF_total

#print axioms compact_MAX_PROOF_R22

theorem compact_PROOF_BYTES_R22
    (t : Translation (fun _ : Unit => compact.PROOF_BYTES)) :
    ∀ u, NoOverflow (t.code u) ∧ wrapping (t.code u) = ok 57607#usize := by
  apply total_refinement_R22 t.code (fun _ => 57607#usize)
  intro u
  exact (t.source u).trans r22_compact_PROOF_BYTES_total

#print axioms compact_PROOF_BYTES_R22

theorem verifier_CHECKPOINT_FIXED_R22
    (t : Translation (fun _ : Unit => verifier.CHECKPOINT_FIXED)) :
    ∀ u, NoOverflow (t.code u) ∧ wrapping (t.code u) = ok 744#usize := by
  apply total_refinement_R22 t.code (fun _ => 744#usize)
  intro u
  exact (t.source u).trans r22_verifier_CHECKPOINT_FIXED_total

#print axioms verifier_CHECKPOINT_FIXED_R22

end AspisR1.R22TotalStage2Constants
