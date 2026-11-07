import NMP_prepare.Funs
set_option autoImplicit false
namespace AspisR1.NMP_EmittedConstants
open Aeneas Aeneas.Std Result NMP_prepare
theorem logical_semantic : compact.LOGICAL_SEMANTIC = .ok 13831#usize := by
 unfold compact.LOGICAL_SEMANTIC verifier.SEMANTIC_BYTES
 rfl
theorem logical_y1 : compact.LOGICAL_Y1 = .ok 928#usize := by
 unfold compact.LOGICAL_Y1
 rfl
theorem off_semantic : compact.OFF_SEMANTIC = 16#usize := by
 unfold compact.OFF_SEMANTIC compact.HEADER
 rfl
theorem off_y1 : compact.OFF_Y1 = .ok 7031#usize := by
 unfold compact.OFF_Y1 compact.COMPACT_SEMANTIC compact.SEMANTIC_COMPACT_VALUES
 rw [logical_semantic,off_semantic]
 rfl
theorem off_inactive : compact.OFF_INACTIVE = .ok 7495#usize := by
 unfold compact.OFF_INACTIVE compact.COMPACT_Y1
 rw [off_y1]
 rfl
theorem total : Usize.wrapping_add 13831#usize 928#usize = 14759#usize := by rfl
#print axioms logical_semantic
#print axioms logical_y1
#print axioms off_semantic
#print axioms off_y1
#print axioms off_inactive
#print axioms total
end AspisR1.NMP_EmittedConstants
