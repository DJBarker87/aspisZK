import NGK_COMBINED_IMPORT
set_option autoImplicit false
namespace AspisR1.NHF_ViewConstants
open Aeneas Aeneas.Std Result AspisR1SelectedWideViewV1
/-- Concrete offsets normalize scalar constants only, never input bytes. -/
theorem inactive : compact.OFF_INACTIVE = ok 7495#usize := by
 simp [compact.OFF_INACTIVE,compact.OFF_ROUND0,compact.OFF_FOLDED_ROOT,compact.OFF_ROUND1,compact.OFF_FINAL,compact.OFF_OPENINGS,compact.OFF_Y1,compact.COMPACT_Y1,compact.COMPACT_SEMANTIC,compact.SEMANTIC_COMPACT_VALUES,compact.LOGICAL_SEMANTIC,compact.OFF_SEMANTIC,compact.HEADER,verifier.SEMANTIC_BYTES,compact.FINAL_LEN] <;> scalar_tac
theorem round0 : compact.OFF_ROUND0 = ok 7527#usize := by
 simp [compact.OFF_INACTIVE,compact.OFF_ROUND0,compact.OFF_FOLDED_ROOT,compact.OFF_ROUND1,compact.OFF_FINAL,compact.OFF_OPENINGS,compact.OFF_Y1,compact.COMPACT_Y1,compact.COMPACT_SEMANTIC,compact.SEMANTIC_COMPACT_VALUES,compact.LOGICAL_SEMANTIC,compact.OFF_SEMANTIC,compact.HEADER,verifier.SEMANTIC_BYTES,compact.FINAL_LEN] <;> scalar_tac
theorem folded : compact.OFF_FOLDED_ROOT = ok 7751#usize := by
 simp [compact.OFF_INACTIVE,compact.OFF_ROUND0,compact.OFF_FOLDED_ROOT,compact.OFF_ROUND1,compact.OFF_FINAL,compact.OFF_OPENINGS,compact.OFF_Y1,compact.COMPACT_Y1,compact.COMPACT_SEMANTIC,compact.SEMANTIC_COMPACT_VALUES,compact.LOGICAL_SEMANTIC,compact.OFF_SEMANTIC,compact.HEADER,verifier.SEMANTIC_BYTES,compact.FINAL_LEN] <;> scalar_tac
theorem round1 : compact.OFF_ROUND1 = ok 7783#usize := by
 simp [compact.OFF_INACTIVE,compact.OFF_ROUND0,compact.OFF_FOLDED_ROOT,compact.OFF_ROUND1,compact.OFF_FINAL,compact.OFF_OPENINGS,compact.OFF_Y1,compact.COMPACT_Y1,compact.COMPACT_SEMANTIC,compact.SEMANTIC_COMPACT_VALUES,compact.LOGICAL_SEMANTIC,compact.OFF_SEMANTIC,compact.HEADER,verifier.SEMANTIC_BYTES,compact.FINAL_LEN] <;> scalar_tac
theorem finalMessage : compact.OFF_FINAL = ok 8007#usize := by
 simp [compact.OFF_INACTIVE,compact.OFF_ROUND0,compact.OFF_FOLDED_ROOT,compact.OFF_ROUND1,compact.OFF_FINAL,compact.OFF_OPENINGS,compact.OFF_Y1,compact.COMPACT_Y1,compact.COMPACT_SEMANTIC,compact.SEMANTIC_COMPACT_VALUES,compact.LOGICAL_SEMANTIC,compact.OFF_SEMANTIC,compact.HEADER,verifier.SEMANTIC_BYTES,compact.FINAL_LEN] <;> scalar_tac
theorem openings : compact.OFF_OPENINGS = ok 10055#usize := by
 simp [compact.OFF_INACTIVE,compact.OFF_ROUND0,compact.OFF_FOLDED_ROOT,compact.OFF_ROUND1,compact.OFF_FINAL,compact.OFF_OPENINGS,compact.OFF_Y1,compact.COMPACT_Y1,compact.COMPACT_SEMANTIC,compact.SEMANTIC_COMPACT_VALUES,compact.LOGICAL_SEMANTIC,compact.OFF_SEMANTIC,compact.HEADER,verifier.SEMANTIC_BYTES,compact.FINAL_LEN] <;> scalar_tac
#print axioms inactive
#print axioms round0
#print axioms folded
#print axioms round1
#print axioms finalMessage
#print axioms openings
end AspisR1.NHF_ViewConstants
