import JHb_S2K_ResultWholeNative
set_option autoImplicit false
namespace NEY_ResultConstants
open Aeneas Aeneas.Std AspisR1TerminalDecoder
open pool_v1.pair_forest_terminal

theorem layout :
    POOL_V1_PAIR_FOREST_TERMINAL_RESULT_MAGIC.val=[65#u8,83#u8,82#u8,56#u8] ∧
    RESULT_MASTER_OFFSET=8#usize ∧ RESULT_SELECTED_LANE_OFFSET=40#usize ∧
    RESULT_NULLIFIER_OFFSET=72#usize ∧ RESULT_AFTERSTATE_OFFSET=104#usize := by
  unfold POOL_V1_PAIR_FOREST_TERMINAL_RESULT_MAGIC RESULT_MASTER_OFFSET
    RESULT_SELECTED_LANE_OFFSET RESULT_NULLIFIER_OFFSET RESULT_AFTERSTATE_OFFSET
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

/-- The complete native window partition has no gap or overlap. -/
theorem partition (k : Nat) (inside : k<792) :
    k<4 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨
    (8≤k ∧ k<40) ∨ (40≤k ∧ k<72) ∨ (72≤k ∧ k<104) ∨
    (104≤k ∧ k<792) := by omega

#print axioms layout
#print axioms partition
end NEY_ResultConstants
