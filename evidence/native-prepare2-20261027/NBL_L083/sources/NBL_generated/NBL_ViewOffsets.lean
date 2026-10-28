import NBA_WideView
set_option autoImplicit false
namespace AspisR1.NBL_ViewOffsets
open Aeneas Aeneas.Std Result AspisR1SelectedWideViewV1

/-- Small closed offsets only; no recurrence or large generated term. -/
theorem source :
    compact.OFF_INACTIVE=ok 7495#usize ∧ compact.OFF_ROUND0=ok 7527#usize ∧
    compact.OFF_FOLDED_ROOT=ok 7751#usize ∧ compact.OFF_ROUND1=ok 7783#usize ∧
    compact.OFF_FINAL=ok 8007#usize ∧ compact.OFF_OPENINGS=ok 10055#usize := by
  unfold compact.OFF_OPENINGS compact.OFF_FINAL compact.OFF_ROUND1 compact.OFF_FOLDED_ROOT
    compact.OFF_ROUND0 compact.OFF_INACTIVE compact.OFF_Y1 compact.COMPACT_Y1
    compact.COMPACT_SEMANTIC compact.OFF_SEMANTIC compact.HEADER
    compact.SEMANTIC_COMPACT_VALUES compact.LOGICAL_SEMANTIC verifier.SEMANTIC_BYTES compact.FINAL_LEN
  decide

#print axioms source
end AspisR1.NBL_ViewOffsets
