import AuS1_Offsets
set_option autoImplicit false
namespace AspisR1.NBL_ViewOffsets
open Aeneas Aeneas.Std Result AspisR1SelectedWideViewV1

theorem final : compact.OFF_FINAL=ok 8007#usize := by
  unfold compact.OFF_FINAL
  rw [AuS1_Offsets.round1]
  simp only [bind_tc_ok]
  exact AuS1_Offsets.add _ _ _ (by scalar_tac) (by scalar_tac)

theorem openings : compact.OFF_OPENINGS=ok 10055#usize := by
  unfold compact.OFF_OPENINGS compact.FINAL_LEN
  rw [AuS1_Offsets.mul 64#usize 32#usize 2048#usize (by scalar_tac) (by scalar_tac),final]
  simp only [bind_tc_ok]
  exact AuS1_Offsets.add _ _ _ (by scalar_tac) (by scalar_tac)

/-- Reuse the unchanged checked selected-parser constants; only the last two
offsets extend its existing chain. -/
theorem source :
    compact.OFF_INACTIVE=ok 7495#usize ∧ compact.OFF_ROUND0=ok 7527#usize ∧
    compact.OFF_FOLDED_ROOT=ok 7751#usize ∧ compact.OFF_ROUND1=ok 7783#usize ∧
    compact.OFF_FINAL=ok 8007#usize ∧ compact.OFF_OPENINGS=ok 10055#usize :=
  ⟨AuS1_Offsets.inactive,AuS1_Offsets.round0,AuS1_Offsets.folded,AuS1_Offsets.round1,final,openings⟩

#print axioms final
#print axioms openings
#print axioms source
end AspisR1.NBL_ViewOffsets
