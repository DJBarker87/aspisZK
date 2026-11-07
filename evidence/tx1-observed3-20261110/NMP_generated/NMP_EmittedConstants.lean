import NMP_prepare.Funs
import NMP_UsizeExact
set_option autoImplicit false
namespace AspisR1.NMP_EmittedConstants
open Aeneas Aeneas.Std Result NMP_prepare
theorem logical_semantic : compact.LOGICAL_SEMANTIC = .ok 13831#usize := by
 unfold compact.LOGICAL_SEMANTIC verifier.SEMANTIC_BYTES
 rw [NMP_UsizeExact.mul 29#usize 32#usize 928#usize (by scalar_tac)]
 simp only [NMP_DirectBind.ok,bind_tc_ok]
 exact NMP_UsizeExact.add _ _ _ (by scalar_tac)
theorem logical_y1 : compact.LOGICAL_Y1 = .ok 928#usize := by
 unfold compact.LOGICAL_Y1
 exact NMP_UsizeExact.mul _ _ _ (by scalar_tac)
theorem off_semantic : compact.OFF_SEMANTIC = 16#usize := by
 unfold compact.OFF_SEMANTIC compact.HEADER
 rfl
theorem off_y1 : compact.OFF_Y1 = .ok 7031#usize := by
 unfold compact.OFF_Y1 compact.COMPACT_SEMANTIC compact.SEMANTIC_COMPACT_VALUES
 rw [logical_semantic,off_semantic]
 simp only [NMP_UsizeExact.mul 10#usize 28#usize 280#usize (by scalar_tac),
  NMP_UsizeExact.add 1#usize 280#usize 281#usize (by scalar_tac),
  NMP_UsizeExact.add 87#usize 29#usize 116#usize (by scalar_tac),
  NMP_UsizeExact.add 281#usize 116#usize 397#usize (by scalar_tac),
  NMP_UsizeExact.add 397#usize 29#usize 426#usize (by scalar_tac),
  NMP_UsizeExact.mul 16#usize 426#usize 6816#usize (by scalar_tac),
  NMP_UsizeExact.sub 13831#usize 6816#usize 7015#usize (by scalar_tac) (by scalar_tac),
  NMP_UsizeExact.add 16#usize 7015#usize 7031#usize (by scalar_tac),
  NMP_DirectBind.ok,bind_tc_ok]
theorem off_inactive : compact.OFF_INACTIVE = .ok 7495#usize := by
 unfold compact.OFF_INACTIVE compact.COMPACT_Y1
 rw [off_y1,NMP_UsizeExact.mul 29#usize 16#usize 464#usize (by scalar_tac)]
 simp only [NMP_DirectBind.ok,bind_tc_ok]
 exact NMP_UsizeExact.add _ _ _ (by scalar_tac)
theorem total : Usize.wrapping_add 13831#usize 928#usize = 14759#usize :=
 NMP_UsizeExact.wrapping_add _ _ _ (by scalar_tac)
#print axioms logical_semantic
#print axioms logical_y1
#print axioms off_semantic
#print axioms off_y1
#print axioms off_inactive
#print axioms total
end AspisR1.NMP_EmittedConstants
