import PCB_SmallStatementRef.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCB_SmallStatementLaws
open PCB_SmallStatementRef.pool_v1

theorem sentinel (leaf : pair_tree_profile.PoolV1PairLeafWitnessV1) :
    pair_tree_profile.PCB_221.reference leaf =
      ok (leaf.second_commitment.val[7]'(by have := leaf.second_commitment.property; simp_all)) := by
  obtain ⟨out,h,hv⟩ := WP.spec_imp_exists
    (Array.index_usize_spec leaf.second_commitment 7#usize (by scalar_tac))
  simp only [pair_tree_profile.PCB_221.reference, h]
  congr 1

theorem full (page : root_history.RootHistoryPageV1) :
    root_history.PCB_242.reference page = ok (decide (page.filled.val = 256)) := by
  unfold root_history.PCB_242.reference
  congr 1
  by_cases h : page.filled = 256#u16
  · have v : page.filled.val = 256 := by scalar_tac
    simp [h,v]
  · have v : page.filled.val ≠ 256 := by scalar_tac
    simp [h,v]

#print axioms sentinel
#print axioms full
end PCB_SmallStatementLaws
