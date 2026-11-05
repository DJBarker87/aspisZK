import NGK_COMBINED_IMPORT
set_option autoImplicit false
namespace AspisR1.NHF_ViewConstants
open Aeneas Aeneas.Std Result AspisR1SelectedWideViewV1
/-- Concrete offsets normalize scalar constants only, never input bytes. -/
theorem inactive : compact.OFF_INACTIVE = ok 7495#usize := by decide
theorem round0 : compact.OFF_ROUND0 = ok 7527#usize := by decide
theorem folded : compact.OFF_FOLDED_ROOT = ok 7751#usize := by decide
theorem round1 : compact.OFF_ROUND1 = ok 7783#usize := by decide
theorem finalMessage : compact.OFF_FINAL = ok 8007#usize := by decide
theorem openings : compact.OFF_OPENINGS = ok 10055#usize := by decide
#print axioms inactive
#print axioms round0
#print axioms folded
#print axioms round1
#print axioms finalMessage
#print axioms openings
end AspisR1.NHF_ViewConstants
